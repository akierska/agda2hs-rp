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
import qualified Agda2Hs.Language.Haskell as Hs
import Agda.Syntax.Common.Pretty
import Agda2Hs.Compile.Type (compileType)
import Agda2Hs.Language.Haskell.Utils ( hsName )
import Agda2Hs.Language.Haskell ( pp, hsError )

decPath :: String
decPath = "Haskell.Extra.Dec.Def.Dec"

compileProp :: Definition -> C [Hs.Decl ()]
compileProp def@Defn{..} = do
    let name = propName $ qnameName defName
    let (tel, concl) = splitTelescope defType

    importDec
    decConcl <- wrapDec concl
    typeSig <- compileTypeSig name tel decConcl
    -- body <- compileBody name tel decConcl

    let body = hsError $ "postulate: " ++ pp typeSig
    return [typeSig, Hs.FunBind () [Hs.Match () name [] (Hs.UnGuardedRhs () body) Nothing] ]


propName :: Name -> Hs.Name ()
propName name = hsName $ "prop_" ++ prettyShow name

-- Splits a type into its parameter bindings and conclusion.
splitTelescope :: Type -> (Telescope, Type)
splitTelescope ty = let TelV tel concl = telView' ty in (tel, concl)

compileTypeSig :: Hs.Name () -> Telescope -> Type -> C (Hs.Decl ())
compileTypeSig name tel concl = do
    ty <- compileType $ unEl $ telePi tel concl
    return $ Hs.TypeSig () [name] ty

compileBody :: Hs.Name () -> Telescope -> Type -> C (Hs.Decl ())
compileBody = undefined

-- Imports Haskell.Extra.Dec.{Def,Instances} into scope
importDec :: C ()
importDec = do
    let haskellExtra = AN.Qual (AC.simpleName "Haskell") . AN.Qual (AC.simpleName "Extra") . AN.Qual (AC.simpleName "Dec")
        directives  = ImportDirective noRange UseEverything [] [] Nothing
        importDecl q = [AC.Import noRange (haskellExtra q) Nothing AC.DontOpen directives]
        run ds = case fst $ runNice (NiceEnv True AC.NoWhere_) $ niceDeclarations empty $ importDecl ds of
                   Left _    -> __IMPOSSIBLE__
                   Right ds' -> liftTCM $ toAbstract ds'
    run $ AC.QName $ AC.simpleName "Def"
    run $ AC.QName $ AC.simpleName "Instances"

    -- Programmatically imported modules don't get properly resolved by agda2hs (inline pragma is not processed)
    -- That's why we need to mark it as inline explicitly below
    decName <- resolveStringName decPath
    addInlineSymbols [decName]

-- Wraps a proposition type P into Dec P.
wrapDec :: Type -> C Type
wrapDec t = do
  dec <- resolveStringName decPath
  level <- liftTCM newLevelMeta
  let vArg = defaultArg
      hArg = setHiding Hidden . vArg
  return $ t {unEl = Def dec $ map Apply [hArg $ Level level, vArg $ unEl t]}

