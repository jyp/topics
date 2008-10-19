
This directory contains various implementations of parser combinators.

* [An implementation of the exact stuff presented in the Polish Parsers](master/Polish.hs)
* [A copy of Koen's Parsek library](master/Parsek.hs)
* [Simple Polish Parsers](master/SimplePolish.hs), My (simplified/clarified) version of the Polish combinators
* [Incremental Parsing with error correction](master/IncrementalParserWithGeneralizedErrorCorrection.hs), 
  based on the Simple Polish Parsers
* [Enhanced ways to manipulate the Polish representation](master/Polish.hs)
* [Manipulation of polish expressions in a fully typed way](master/Polish.agda)

And some less interesting stuff:

* [Some crappy version of error correction](master/IncrementalParserWithErrorCorrectionHack.hs), 
  and a [test case](master/TestCase1.hs) where it fails .

I'm not sure why this is here:

references:
 - [left fold]
[left fold]: http://okmij.org/ftp/Streams.html#iteratee
