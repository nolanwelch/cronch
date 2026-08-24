%% Reflection the invariant tests in test/invariant_test.gleam need: reading a
%% source file to count and inspect its lines, and running a command in a
%% genuinely fresh operating-system process.
%%
%% Nothing in the trusted computing base calls any of it. It lives in src/
%% rather than test/ only because Gleam compiles Erlang sources from src/.
-module(cronch_inspect_ffi).

-export([read_source/1, os_run/1]).

%% Read a source file as text. Error(Nil) if it is missing or not UTF-8, so a
%% test that cannot find the kernel fails rather than silently measuring
%% nothing.
read_source(Path) ->
    case file:read_file(Path) of
        {ok, Bytes} ->
            case unicode:characters_to_binary(Bytes, utf8, utf8) of
                Text when is_binary(Text) -> {ok, Text};
                _ -> {error, nil}
            end;
        {error, _} ->
            {error, nil}
    end.

%% Run a shell command and return its combined output. Used to start a second
%% BEAM -- a real OS process with its own scheduler, heap and module table, not
%% merely a second process inside this one.
os_run(Command) ->
    unicode:characters_to_binary(os:cmd(unicode:characters_to_list(Command))).
