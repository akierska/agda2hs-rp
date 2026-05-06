module Agda2Hs.Compile.Property where

import Agda.Compiler.Backend (Definition)
import Agda2Hs.Compile.Types
import qualified Agda2Hs.Language.Haskell as Hs

compileProp :: Definition -> C [Hs.Decl ()]
compileProp = undefined
