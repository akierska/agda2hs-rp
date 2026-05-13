module Agda2Hs.Compile.Property where

import Data.Map (empty)

import Agda.Compiler.Backend (Definition, TCM)
import Agda.Interaction.BasicOps
import Agda.Syntax.Common
import Agda.Syntax.Concrete.Definitions (NiceEnv (NiceEnv), niceDeclarations, runNice)
import Agda.Syntax.Internal
import Agda.Syntax.Position (noRange)
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad
import Agda.Syntax.Translation.ConcreteToAbstract (ToAbstract (toAbstract))
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import qualified Agda.Syntax.Concrete as AC
import qualified Agda.Syntax.Concrete.Name as AN

import Agda2Hs.AgdaUtils (resolveStringName)
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.Language.Haskell (hsName)
import qualified Agda2Hs.Language.Haskell as Hs
import Agda.Syntax.Common.Pretty

compileProp :: Definition -> C [Hs.Decl ()]
compileProp def@Defn{..} = do
    let name = propName $ qnameName defName

    liftTCM importDec
    (tel, concl) <- splitTelescope defType
    decConcl <- wrapDec concl
    typeSig <- compileTypeSig name tel decConcl
    body <- compileBody name tel decConcl

    return [typeSig, body]

-- Splits a type into (parameter telescope, conclusion type).
splitTelescope :: Type -> C (Telescope, Type)
splitTelescope = undefined

propName :: Name -> String
propName name = "prop_" ++ prettyShow name

compileTypeSig :: String -> Telescope -> Type -> C (Hs.Decl ())
compileTypeSig = undefined

compileBody :: String -> Telescope -> Type -> C (Hs.Decl ())
compileBody = undefined

-- Imports Haskell.Extra.Dec.{Def,Instances} into scope.
-- based on Agda.Syntax.Translation.ConcreteToAbstract.importPrimitives
importDec :: TCM ()
importDec = do
  let haskellExtra = AN.Qual (AC.simpleName "Haskell") . AN.Qual (AC.simpleName "Extra") . AN.Qual (AC.simpleName "Dec")
      directives = ImportDirective noRange UseEverything [] [] Nothing
      importDecl q = [AC.Import noRange (haskellExtra q) Nothing AC.DontOpen directives]
      run ds = case fst $ runNice (NiceEnv True AC.NoWhere_) $ niceDeclarations empty $ importDecl ds of
        Left _ -> __IMPOSSIBLE__
        Right ds -> toAbstract ds
  run $ AC.QName $ AC.simpleName "Def"
  run $ AC.QName $ AC.simpleName "Instances"
  return ()

-- Wraps type t with Dec (t -> Dec t)
wrapDec :: Type -> C Type
wrapDec t = do
  dec <- resolveStringName "Haskell.Extra.Dec.Def.Dec"
  level <- liftTCM newLevelMeta
  let vArg = defaultArg
      hArg = setHiding Hidden . vArg
  return $ t {unEl = Def dec $ map Apply [hArg $ Level level, vArg $ unEl t]}

