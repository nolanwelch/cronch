/// Elaboration: surface `Expr`/`Item` -> core de Bruijn `Term`s. UNTRUSTED;
/// the kernel re-checks everything this produces.
///
/// Enforces the grammar wall: a `trusted` form is an error in proof position.
/// Proof position: `define` bodies. Runtime position: `runtime` bodies.
import cronch/digest
import cronch/hash
import cronch/syntax/parse.{
  type Expr, type HoleSpec, type Item, type ProcRef, Define, EApp, EArrow,
  EConst, EEq, EHole, ELam, EName, EPi, ERefl, ESort, ETrusted, EVarIx, HoleItem,
  HoleName, HoleNumber, ProcDigest, ProcName,
}
import cronch/term
import gleam/dict
import gleam/list
import gleam/option.{type Option, None, Some}

// ── Types ─────────────────────────────────────────────────────────────────────

/// Whether elaboration is in proof or runtime position.
pub type Position {
  Proof
  Runtime
}

pub type ElabError {
  /// A name resolved to neither a bound variable nor a top-level definition.
  UnboundName(String)
  /// `trusted` appeared in proof position (grammar-wall violation).
  TrustedInProofPosition
  /// A `trusted` procedure name did not resolve to a defined object.
  UnboundProc(String)
  /// A top-level name was defined twice.
  DuplicateName(String)
}

/// Allocates ids for named holes; numeric holes use their literal id.
pub type HoleAlloc {
  HoleAlloc(next: Int, named: dict.Dict(String, Int))
}

pub fn empty_hole_alloc() -> HoleAlloc {
  HoleAlloc(next: 0, named: dict.new())
}

fn allocate_id(hole_alloc: HoleAlloc, spec: HoleSpec) -> #(Int, HoleAlloc) {
  case spec {
    HoleNumber(n) -> #(n, hole_alloc)
    HoleName(s) ->
      case dict.get(hole_alloc.named, s) {
        Ok(id) -> #(id, hole_alloc)
        Error(_) -> {
          // Named holes get ids from a high base to avoid collisions with
          // typical small explicit ids.
          let id = 1_000_000 + hole_alloc.next
          let hole_alloc =
            HoleAlloc(
              next: hole_alloc.next + 1,
              named: dict.insert(hole_alloc.named, s, id),
            )
          #(id, hole_alloc)
        }
      }
  }
}

/// Top-level name -> content address map.
pub type Environment =
  dict.Dict(String, digest.Digest)

/// Resolved module store: content address -> term.
pub type Store =
  fn(digest.Digest) -> Option(term.Term)

// ── Per-entry result ──────────────────────────────────────────────────────────

pub type EntryKind {
  DefineKind
  RuntimeKind
  HoleKind
}

pub type ElabEntry {
  ElabEntry(
    name: String,
    kind: EntryKind,
    position: Position,
    declared_typ: term.Term,
    term: term.Term,
    address: digest.Digest,
  )
}

/// A fully elaborated module.
pub type ElabModule {
  ElabModule(store: Store, environment: Environment, entries: List(ElabEntry))
}

// ── Elaboration ───────────────────────────────────────────────────────────────

/// Elaborate a single expression into a core term.
/// `scope` is a list of bound names, head = innermost (Var(0)).
pub fn elaborate_expr(
  e: Expr,
  scope: List(String),
  environment: Environment,
  position: Position,
  holes: HoleAlloc,
) -> Result(#(term.Term, HoleAlloc), ElabError) {
  case e {
    EName(s) ->
      case find_var(scope, s, 0) {
        Some(idx) -> Ok(#(term.Var(idx), holes))
        None ->
          case dict.get(environment, s) {
            Ok(d) -> Ok(#(term.Const(d), holes))
            Error(_) -> Error(UnboundName(s))
          }
      }

    EVarIx(k) -> Ok(#(term.Var(k), holes))

    ESort(u) -> Ok(#(term.Sort(u), holes))

    EConst(d) -> Ok(#(term.Const(d), holes))

    EArrow(a, b) -> {
      use #(da, holes) <- try_elab(elaborate_expr(
        a,
        scope,
        environment,
        position,
        holes,
      ))
      use #(db, holes) <- try_elab(elaborate_expr(
        b,
        ["_", ..scope],
        environment,
        position,
        holes,
      ))
      Ok(#(term.Pi(da, db), holes))
    }

    EPi(name, a, b) -> {
      use #(da, holes) <- try_elab(elaborate_expr(
        a,
        scope,
        environment,
        position,
        holes,
      ))
      use #(db, holes) <- try_elab(elaborate_expr(
        b,
        [name, ..scope],
        environment,
        position,
        holes,
      ))
      Ok(#(term.Pi(da, db), holes))
    }

    ELam(name, a, b) -> {
      use #(da, holes) <- try_elab(elaborate_expr(
        a,
        scope,
        environment,
        position,
        holes,
      ))
      use #(db, holes) <- try_elab(elaborate_expr(
        b,
        [name, ..scope],
        environment,
        position,
        holes,
      ))
      Ok(#(term.Lam(da, db), holes))
    }

    EApp(f, a) -> {
      use #(df, holes) <- try_elab(elaborate_expr(
        f,
        scope,
        environment,
        position,
        holes,
      ))
      use #(da, holes) <- try_elab(elaborate_expr(
        a,
        scope,
        environment,
        position,
        holes,
      ))
      Ok(#(term.App(df, da), holes))
    }

    EEq(typ, a, b) -> {
      use #(dt, holes) <- try_elab(elaborate_expr(
        typ,
        scope,
        environment,
        position,
        holes,
      ))
      use #(da, holes) <- try_elab(elaborate_expr(
        a,
        scope,
        environment,
        position,
        holes,
      ))
      use #(db, holes) <- try_elab(elaborate_expr(
        b,
        scope,
        environment,
        position,
        holes,
      ))
      Ok(#(term.Eq(dt, da, db), holes))
    }

    ERefl(typ, a) -> {
      use #(dt, holes) <- try_elab(elaborate_expr(
        typ,
        scope,
        environment,
        position,
        holes,
      ))
      use #(da, holes) <- try_elab(elaborate_expr(
        a,
        scope,
        environment,
        position,
        holes,
      ))
      Ok(#(term.Refl(dt, da), holes))
    }

    EHole(spec, goal) -> {
      let #(id, holes) = allocate_id(holes, spec)
      use #(dg, holes) <- try_elab(elaborate_expr(
        goal,
        scope,
        environment,
        position,
        holes,
      ))
      Ok(#(term.Hole(id, dg), holes))
    }

    ETrusted(host, proc_ref, args_expr, rty_expr) -> {
      case position {
        Proof -> Error(TrustedInProofPosition)
        Runtime -> {
          use proc_digest <- try_elab(resolve_proc(proc_ref, environment))
          use #(da, holes) <- try_elab(elaborate_expr(
            args_expr,
            scope,
            environment,
            position,
            holes,
          ))
          use #(dr, holes) <- try_elab(elaborate_expr(
            rty_expr,
            scope,
            environment,
            position,
            holes,
          ))
          Ok(#(term.Trusted(host, proc_digest, da, dr), holes))
        }
      }
    }
  }
}

fn resolve_proc(
  proc_ref: ProcRef,
  environment: Environment,
) -> Result(digest.Digest, ElabError) {
  case proc_ref {
    ProcDigest(d) -> Ok(d)
    ProcName(n) ->
      case dict.get(environment, n) {
        Ok(d) -> Ok(d)
        Error(_) -> Error(UnboundProc(n))
      }
  }
}

/// Elaborate a closed expression (empty scope, empty environment) at the given position.
pub fn elaborate_closed(
  e: Expr,
  position: Position,
) -> Result(term.Term, ElabError) {
  case elaborate_expr(e, [], dict.new(), position, empty_hole_alloc()) {
    Ok(#(t, _)) -> Ok(t)
    Error(err) -> Error(err)
  }
}

/// Elaborate a parsed module, building the store and environment.
/// Each definition is content-addressed and registered so later items may
/// reference it by name (becoming a `Const`).
pub fn elaborate_module(items: List(Item)) -> Result(ElabModule, ElabError) {
  do_elab_module(items, dict.new(), dict.new(), [], empty_hole_alloc())
}

fn do_elab_module(
  items: List(Item),
  store_dict: dict.Dict(digest.Digest, term.Term),
  environment: Environment,
  entries: List(ElabEntry),
  holes: HoleAlloc,
) -> Result(ElabModule, ElabError) {
  case items {
    [] -> {
      let store = fn(d: digest.Digest) {
        dict.get(store_dict, d) |> option_of_result
      }
      Ok(ElabModule(
        store: store,
        environment: environment,
        entries: list.reverse(entries),
      ))
    }

    [Define(name, typ, body), ..rest] ->
      elab_def(
        name,
        typ,
        body,
        Proof,
        DefineKind,
        rest,
        store_dict,
        environment,
        entries,
        holes,
      )

    [parse.Runtime(name, typ, body), ..rest] ->
      elab_def(
        name,
        typ,
        body,
        Runtime,
        RuntimeKind,
        rest,
        store_dict,
        environment,
        entries,
        holes,
      )

    [HoleItem(name, typ), ..rest] -> {
      case dict.has_key(environment, name) {
        True -> Error(DuplicateName(name))
        False -> {
          use #(declared_typ, holes) <- try_elab(elaborate_expr(
            typ,
            [],
            environment,
            Proof,
            holes,
          ))
          let #(id, holes) = allocate_id(holes, HoleName(name))
          let t = term.Hole(id, declared_typ)
          let address = hash.hash(digest.Blake3, t)
          let store_dict = dict.insert(store_dict, address, t)
          let environment = dict.insert(environment, name, address)
          let entry =
            ElabEntry(
              name: name,
              kind: HoleKind,
              position: Proof,
              declared_typ: declared_typ,
              term: t,
              address: address,
            )
          do_elab_module(
            rest,
            store_dict,
            environment,
            [entry, ..entries],
            holes,
          )
        }
      }
    }
  }
}

fn elab_def(
  name: String,
  typ: Expr,
  body: Expr,
  position: Position,
  kind: EntryKind,
  rest: List(Item),
  store_dict: dict.Dict(digest.Digest, term.Term),
  environment: Environment,
  entries: List(ElabEntry),
  holes: HoleAlloc,
) -> Result(ElabModule, ElabError) {
  case dict.has_key(environment, name) {
    True -> Error(DuplicateName(name))
    False -> {
      use #(declared_typ, holes) <- try_elab(elaborate_expr(
        typ,
        [],
        environment,
        position,
        holes,
      ))
      use #(t, holes) <- try_elab(elaborate_expr(
        body,
        [],
        environment,
        position,
        holes,
      ))
      let address = hash.hash(digest.Blake3, t)
      let store_dict = dict.insert(store_dict, address, t)
      let environment = dict.insert(environment, name, address)
      let entry =
        ElabEntry(
          name: name,
          kind: kind,
          position: position,
          declared_typ: declared_typ,
          term: t,
          address: address,
        )
      do_elab_module(rest, store_dict, environment, [entry, ..entries], holes)
    }
  }
}

// ── Helpers ───────────────────────────────────────────────────────────────────

fn find_var(scope: List(String), name: String, idx: Int) -> Option(Int) {
  case scope {
    [] -> None
    [n, ..] if n == name -> Some(idx)
    [_, ..rest] -> find_var(rest, name, idx + 1)
  }
}

fn try_elab(
  r: Result(a, ElabError),
  f: fn(a) -> Result(b, ElabError),
) -> Result(b, ElabError) {
  case r {
    Error(e) -> Error(e)
    Ok(a) -> f(a)
  }
}

fn option_of_result(r: Result(a, e)) -> Option(a) {
  case r {
    Ok(a) -> Some(a)
    Error(_) -> None
  }
}
