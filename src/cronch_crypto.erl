-module(cronch_crypto).
-export([verify_ed25519/3, sign_ed25519/2, generate_keypair/0]).

%% verify_ed25519(Msg, Signature, PubKey) -> boolean()
%% Verify an Ed25519 signature. Fails closed: any error returns false.
verify_ed25519(Msg, Sig, PubKey) ->
    try
        crypto:verify(eddsa, none, Msg, Sig, [PubKey, ed25519])
    catch
        _:_ -> false
    end.

%% sign_ed25519(Msg, PrivKey) -> Signature (64 bytes)
sign_ed25519(Msg, PrivKey) ->
    crypto:sign(eddsa, none, Msg, [PrivKey, ed25519]).

%% generate_keypair() -> {PubKey, PrivKey}  (both 32-byte binaries)
generate_keypair() ->
    crypto:generate_key(eddsa, ed25519).
