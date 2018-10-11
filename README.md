PSQ
=====

Priority search queue.

It is a port of Haskell [psqueues](http://hackage.haskell.org/package/psqueues) package
to Erlang.

Build
-----

    $ rebar3 compile

Usage
-----

Look at [pid_psq](src/pid_psq.erl) as an example how to use this data structure
for spreading jobs between workers identified by `pid`


