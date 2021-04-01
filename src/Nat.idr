module Nat

import Data.Nat

%default total

export
interchange : (a, b, c, d : Nat) -> (a+b)+(c+d) = (a+c)+(b+d)
interchange a b c d = rewrite sym $ plusAssociative a b (c+d) in
                      rewrite plusAssociative b c d in
                      rewrite plusCommutative b c in
                      rewrite sym $ plusAssociative c b d in
                      plusAssociative a c (b+d)