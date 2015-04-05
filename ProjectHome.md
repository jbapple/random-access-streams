This project provides an implementation of infinite-length lists that aims to improve on:

  * [Data.Stream](http://hackage.haskell.org/cgi-bin/hackage-scripts/package/Stream) by offering a `O(lg n)` bound for `(!!)`
  * [Data.Sequence](http://www.haskell.org/ghc/docs/latest/html/libraries/containers/Data-Sequence.html) by allowing lists to be infinite.

Unfortunately, `cons` is an `O(lg k)` (where `k` elements of the stream are eventually forced) operation, while is it `O(1)` on regular lists, Data.Sequences, and Data.Streams.

The internal representation uses Braun trees (or Braun streams, in this case).

[The latest API documentation is here.](http://random-access-streams.googlecode.com/svn/trunk/dist/doc/html/RandomAccessStream/Data-RandomAccessStream.html)

[The Coq proofs are here.](https://code.google.com/p/random-access-streams/source/browse/trunk/doc/computer-proofs)