{-# LANGUAGE ScopedTypeVariables #-}

module Smuggler.Compress
       ( compressableAdjacentImports
       , compressImports
       ) where

import ApiAnnotation (AnnKeywordId (..))
import qualified Data.Set as Set
import HscTypes (ImportedBy (..), ImportedModsVal (..), importedByUser)
import HsExtension (GhcPs, GhcRn, noExt)
import HsImpExp (IE (..), IEWrappedName (..), LImportDecl, ideclName, ideclHiding, ieName)
import HsSyn (HsModule (..))
import Module (Module (..), ModuleName, moduleName)
import Name (Name, occName, occNameFS)
import RdrName (GlobalRdrElt (..), globalRdrEnvElts, mkVarUnqual)
import SrcLoc (Located, GenLocated (..), unLoc)

import Language.Haskell.GHC.ExactPrint (Anns)
import Language.Haskell.GHC.ExactPrint.Transform (TransformT, addSimpleAnnT, addTrailingCommaT, runTransform, uniqueSrcSpanT)
import Language.Haskell.GHC.ExactPrint.Types (DeltaPos (..), KeywordId (..))

data CanCompress a
  = No
  | Partial (a, a)
  | Full a
  deriving (Eq, Ord)

compressable
  :: Ord a => Set.Set a
  -> Set.Set a
  -> CanCompress (Set.Set a)
compressable i es
  | Set.disjoint i es = No
  | Set.isProperSubsetOf i es = Full i
  | otherwise = Partial (Set.difference i es, Set.intersection i es)

-- From list of imports, determine if any adjacent imports
-- is compressable
compressableAdjacentImports
  :: [LImportDecl GhcRn]
  -> [(Module, [ImportedBy])]
  -> [CanCompress (Set.Set Name)]
compressableAdjacentImports [i, j] all_imports
  = compressable (getUserImportNames j) (getFullImports i all_imports)
  : compressableAdjacentImports [] all_imports
compressableAdjacentImports (i : j : rest) all_imports
  = compressable (getUserImportNames j) (getFullImports i all_imports)
  : compressableAdjacentImports (j : rest) all_imports
compressableAdjacentImports _ _ = []

-- some types for readability
type Merges = [CanCompress (Set.Set Name)]
type Imports = [LImportDecl GhcPs]
type AnnsAst = (Anns, Located (HsModule GhcPs))
type Rewrite = AnnsAst -> AnnsAst

-- Given a set of merge actions,
-- a list of imports,
-- an accumulator,
-- an initial (ann, ast)
-- produce a final (ann', ast')
compressImports :: Merges -> Imports -> Imports -> Rewrite
compressImports
  (this : next : rest) (i1@(L l1 imp1) : i2@(L l2 imp2) : is)
  acc (anns, ast) = do
  let (L astLoc hsMod) = ast
  case this of
    No -> compressImports (next : rest) (i2 : is) (acc ++ [i1]) (anns, ast)
    Full mergeDecls -> do
      let (mDecls, _, _) = runTransform anns (mapM mkIEVarFromName (Set.toList mergeDecls))
          Just (_, L locHiding currentDecls) = ideclHiding imp1
          imp1' = L l1 imp1 { ideclHiding = Just (True, L locHiding (currentDecls ++ mDecls)) }
          mergeImportDeclsFull imp1' = do
            let hsMod' = hsMod { hsmodImports = acc ++ [imp1'] ++ is }
            addTrailingCommaT (last currentDecls)
            mapM_ addImportDeclAnn mDecls
            return (L astLoc hsMod')
          (ast', (anns', _), _) = runTransform anns (mergeImportDeclsFull imp1')
      compressImports rest is (acc ++ [imp1']) (anns', ast')
    Partial (keepDecls, mergeDecls) -> do
      let (mDecls, _, _)
            = runTransform anns (mapM mkIEVarFromName (Set.toList mergeDecls))
          (kDecls, _, _)
            = runTransform anns (mapM mkIEVarFromName (Set.toList keepDecls))
          Just (_, L locHiding currentDecls) = ideclHiding imp1
          Just (_, L locHiding2 _) = ideclHiding imp2
          imp1' = L l1 imp1 { ideclHiding = Just (True, L locHiding (currentDecls ++ mDecls)) }
          imp2' = L l2 imp2 { ideclHiding = Just (True, L locHiding2 kDecls) }
          mergeImportDeclsPartial imp1' imp2' = do
            let hsMod' = hsMod { hsmodImports = acc ++ [imp1', imp2'] ++ is }
            addTrailingCommaT (last currentDecls)
            mapM_ addImportDeclAnn mDecls
            mapM_ addImportDeclAnn kDecls
            return (L astLoc hsMod')
          (ast', (anns', _), _) = runTransform anns (mergeImportDeclsPartial imp1' imp2')
      compressImports (next : rest) (imp2' : is) (acc ++ [imp1']) (anns', ast')
compressImports [this] [i1@(L l1 imp1), i2@(L l2 imp2)] acc (anns, ast) = do
  let (L astLoc hsMod) = ast
  case this of
    No -> (anns, ast)
    Full mergeDecls -> do
      let (mDecls, _, _) = runTransform anns (mapM mkIEVarFromName (Set.toList mergeDecls))
          Just (_, L locHiding currentDecls) = ideclHiding imp1
          imp1' = L l1 imp1 { ideclHiding = Just (True, L locHiding (currentDecls ++ mDecls)) }
          mergeImportDeclsFull imp1' = do
            let hsMod' = hsMod { hsmodImports = acc ++ [imp1'] }
            addTrailingCommaT (last currentDecls)
            mapM_ addImportDeclAnn mDecls
            return (L astLoc hsMod')
          (ast', (anns', _), _) = runTransform anns (mergeImportDeclsFull imp1')
      (anns', ast')
    Partial (keepDecls, mergeDecls) -> do
      let (mDecls, _, _)
            = runTransform anns (mapM mkIEVarFromName (Set.toList mergeDecls))
          (kDecls, _, _)
            = runTransform anns (mapM mkIEVarFromName (Set.toList keepDecls))
          Just (_, L locHiding currentDecls) = ideclHiding imp1
          Just (_, L locHiding2 _) = ideclHiding imp2
          imp1' = L l1 imp1 { ideclHiding = Just (True, L locHiding (currentDecls ++ mDecls)) }
          imp2' = L l2 imp2 { ideclHiding = Just (True, L locHiding2 kDecls) }
          mergeImportDeclsPartial imp1' imp2' = do
            let hsMod' = hsMod { hsmodImports = acc ++ [imp1', imp2'] }
            addTrailingCommaT (last currentDecls)
            mapM_ addImportDeclAnn mDecls
            mapM_ addImportDeclAnn kDecls
            return (L astLoc hsMod')
          (ast', (anns', _), _) = runTransform anns (mergeImportDeclsPartial imp1' imp2')
      (anns', ast')
compressImports _ _ _ (anns, ast) = (anns, ast)

getFullImports :: LImportDecl GhcRn -> [(Module, [ImportedBy])] -> Set.Set Name
getFullImports user gbl = Set.fromList $ allImports (match gbl needle)
  where
    needle :: ModuleName
    needle = (unLoc . ideclName) (unLoc user)

    -- returns a singleton
    match :: [(Module, [ImportedBy])] -> ModuleName -> [ImportedModsVal]
    match [] _ = []
    match ((m, is) : rest) x
      | moduleName m == x = importedByUser is
      | otherwise = match rest x

    allImports :: [ImportedModsVal] -> [Name]
    allImports [i] = (map gre_name . globalRdrEnvElts) (imv_all_exports i)
    allImports _ = []

getUserImportNames :: LImportDecl GhcRn -> Set.Set Name
getUserImportNames user_import
  = case (ideclHiding . unLoc) user_import of
    Just (_, ls) -> Set.fromList $ map (ieName . unLoc) (unLoc ls)
    Nothing -> Set.empty

-- given a name, construct a LIE
mkIEVarFromName :: Monad m => Name -> TransformT m (Located (IE GhcPs))
mkIEVarFromName name = do
  loc <- uniqueSrcSpanT
  return $ L loc (IEVar noExt (L loc (IEName
    (L loc (mkVarUnqual ((occNameFS . occName) name))))))

addImportDeclAnn :: Monad m => Located (IE GhcPs) -> TransformT m ()
addImportDeclAnn (L _ (IEVar _ (L _ (IEName x))))
  = addSimpleAnnT x
    (DP (0, 0))
    [ (G AnnVal, DP (0, 0)) ]
addImportDeclAnn _ = return ()
