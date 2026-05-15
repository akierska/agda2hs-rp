module Agda2Hs.Compile.Property where

import Control.Monad.Error.Class
import Data.Map (empty)

import Agda.Compiler.Backend (Definition)
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty ( prettyShow )
import qualified Agda.Syntax.Concrete as AC
import Agda.Syntax.Concrete.Definitions (NiceEnv (NiceEnv), niceDeclarations, runNice)
import qualified Agda.Syntax.Concrete.Name as AN
import Agda.Syntax.Internal
import Agda.Syntax.Position (noRange)
import Agda.Syntax.Scope.Base
import Agda.Syntax.Translation.ConcreteToAbstract (ToAbstract (toAbstract))
import Agda.TypeChecking.InstanceArguments
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.Utils.Impossible (__IMPOSSIBLE__)

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Term
import Agda2Hs.Compile.Type (compileType, DomOutput (DOTerm), compileDom)
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import qualified Agda2Hs.Language.Haskell as Hs
import Agda2Hs.Language.Haskell.Utils ( hsName )

decPath :: String
decPath = "Haskell.Extra.Dec.Def.Dec"

compileProp :: Definition -> C [Hs.Decl ()]
compileProp def@Defn{..} = do
    let name = propName $ qnameName defName
    let (tel, concl) = splitTelescope defType

    importDec
    importQuickCheck
    decTy <- wrapDec concl
    sig <- compileTypeSig name tel decTy
    body <- compileBody name tel decTy

    return [sig, body]

propName :: Name -> Hs.Name ()
propName name = hsName $ "prop_" ++ prettyShow name

-- Splits a type into its parameter bindings and conclusion.
splitTelescope :: Type -> (Telescope, Type)
splitTelescope ty = let TelV tel concl = telView' ty in (tel, concl)

compileTypeSig :: Hs.Name () -> Telescope -> Type -> C (Hs.Decl ())
compileTypeSig name tel decTy = do
    ty <- compileType $ unEl $ telePi tel decTy
    return $ Hs.TypeSig () [name] ty

compilePat :: Telescope -> C [Hs.Pat ()]
compilePat EmptyTel = return []
compilePat (ExtendTel a tel) = do
    pat <- compileDom a >>= \case
        DOTerm -> do
            let name = hsName $ absName tel
            checkValidVarName name
            return [Hs.PVar () name]
        _ -> return []
    
    (pat ++) <$> underAbstraction a tel compilePat

compileBody :: Hs.Name () -> Telescope -> Type -> C (Hs.Decl ())
compileBody name tel decTy = do
    hsPats <- compilePat tel
    hsExp <- addContext tel $ liftTCM (findDecInstance decTy) >>= \case
            Nothing -> agda2hsErrorM $ "No Dec instance found for" <+> prettyTCM decTy
            Just decInst -> compileTerm decTy decInst

    return $ Hs.FunBind () [Hs.Match () name hsPats (Hs.UnGuardedRhs () hsExp) Nothing]

-- Imports Haskell.Extra.Dec.{Def} into scope
importDec :: C ()
importDec = do
    let haskellExtra = AN.Qual (AC.simpleName "Haskell") . AN.Qual (AC.simpleName "Extra") . AN.Qual (AC.simpleName "Dec")
        directives  = ImportDirective noRange UseEverything [] [] Nothing
        importDecl q = [AC.Import noRange (haskellExtra q) Nothing AC.DontOpen directives]
        run ds = case fst $ runNice (NiceEnv True AC.NoWhere_) $ niceDeclarations empty $ importDecl ds of
                   Left _    -> __IMPOSSIBLE__
                   Right ds' -> liftTCM $ toAbstract ds'
    run $ AC.QName $ AC.simpleName "Def"

    -- Programmatic imports bypass pragma processing by agda2hs, so dec, which is marked as inline, must be registered manually.
    decName <- resolveStringName decPath
    addInlineSymbols [decName]

importQuickCheck :: C ()
importQuickCheck = do
  tellImport $ Import
    { _importModule    = Hs.ModuleName () "Test.QuickCheck"
    , _importQualified = Unqualified
    , _importParent    = Nothing
    , _importName      = Hs.Ident () "Property"
    , _importNamespace = Hs.NoNamespace ()
    }

-- Wraps a proposition type P into Dec P.
wrapDec :: Type -> C Type
wrapDec t = do
  dec <- resolveStringName decPath
  level <- liftTCM newLevelMeta
  let vArg = defaultArg
      hArg = setHiding Hidden . vArg
  return $ t {unEl = Def dec $ map Apply [hArg $ Level level, vArg $ unEl t]}

-- TODO make this nicer?
findDecInstance :: Type -> TCMT IO (Maybe Term)
findDecInstance t =
  do
    (m, v) <- newInstanceMeta "" t
    findInstance m Nothing
    Just <$> instantiateFull v
    `catchError` return (return Nothing)
