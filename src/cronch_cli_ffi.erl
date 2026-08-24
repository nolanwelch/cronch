%% Hand-rolled FFI for the command line: argument access, file I/O, stderr and
%% exit codes.
%%
%% Gleam's standard library has none of these, and this project takes no new
%% dependencies -- not for argument parsing, not for file access. What is here
%% is the minimum the CLI in src/cronch/cli.gleam needs, wrapped so that every
%% failure comes back as a Gleam `Error(Nil)` rather than an exception. Nothing
%% in the trusted computing base calls any of it.
-module(cronch_cli_ffi).

-export([
    argv/0,
    read_file/1,
    write_file/2,
    list_dir/1,
    ensure_dir/1,
    print_error/1,
    exit_with/1
]).

%% Plain arguments, i.e. whatever followed `--`. Charlists from the runtime,
%% binaries for Gleam.
argv() ->
    [unicode:characters_to_binary(A) || A <- init:get_plain_arguments()].

read_file(Path) ->
    case file:read_file(Path) of
        {ok, Bytes} -> {ok, Bytes};
        {error, _} -> {error, nil}
    end.

write_file(Path, Bytes) ->
    case file:write_file(Path, Bytes) of
        ok -> {ok, nil};
        {error, _} -> {error, nil}
    end.

%% Names only, not paths, sorted so a directory listing is deterministic --
%% the order the filesystem hands entries back is unspecified, and anything
%% derived from an unspecified order is not reproducible.
list_dir(Path) ->
    case file:list_dir(Path) of
        {ok, Names} ->
            {ok, lists:sort([unicode:characters_to_binary(N) || N <- Names])};
        {error, _} ->
            {error, nil}
    end.

%% Create Path and any missing parents. filelib:ensure_dir/1 creates the
%% *parent* of what it is given, hence the trailing dummy component.
ensure_dir(Path) ->
    case filelib:ensure_dir(filename:join(Path, "placeholder")) of
        ok -> {ok, nil};
        {error, _} -> {error, nil}
    end.

print_error(Text) ->
    io:put_chars(standard_error, [Text, $\n]),
    nil.

%% Flush before halting: without it, output written moments earlier can be
%% lost, and a CLI whose exit code and output disagree is worse than useless.
exit_with(Code) ->
    erlang:halt(Code, [{flush, true}]).
