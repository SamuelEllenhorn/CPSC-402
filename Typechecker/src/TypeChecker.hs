module TypeChecker ( typecheck ) where

import AbsCPP
import ErrM
import PrintCPP

import Data.Map ( Map )
import qualified Data.Map as M
import Data.Set ( Set )
import qualified Data.Set as S
import Data.List ( intercalate, intersperse )
import Control.Monad ( foldM, foldM_, forM_, unless )


newtype Alternative a = Alternative [a]
instance Print a => Print (Alternative a) where
    prt i (Alternative xs) = 
        ((foldr (.) id) . (intersperse (doc (showString "/"))) . map (prt i)) xs


typeMismatchError :: (Print e, Print t1, Print t2) => e -> t1 -> t2 -> String
typeMismatchError e tExp tFound = 
    "TYPE ERROR\n\n" ++
    "Expected " ++ printTree e ++ " to have type " ++ printTree tExp ++
    " instead found type " ++ printTree tFound ++ "."


ok :: Err ()
ok = Ok ()


type FunctionType = ([Type], Type)
type Sig = Map Id FunctionType
type Context = Map Id Type
type Env = (Sig, [Context])


lookupFun :: Env -> Id -> Err FunctionType
lookupFun (sig,_) id = case M.lookup id sig of
    Just ty -> return ty
    Nothing -> fail $ "TYPE ERROR\n\n" ++ printTree id ++ " was not declared."


insertFun :: Env -> Id -> FunctionType -> Err Env
insertFun (sig,ctxt) i t = do
    case M.lookup i sig of
        Just _  -> fail $ 
            "TYPE ERROR\n\nFailed to add " 
            ++ printTree i ++ "to the symbol table, as it is already defined"
        Nothing -> return (M.insert i t sig, ctxt)


lookupVar :: Id -> Env -> Err Type
lookupVar i (_,[]) = fail $ "TYPE ERROR\n\n" ++ printTree i ++ " was not declared."
lookupVar i (sig,c:ctxt) = case M.lookup i c of
    (Just f) -> return f
    Nothing -> lookupVar i (sig,ctxt)


insertVar :: Env -> Id -> Type -> Err Env
insertVar (_, []) _ _ = fail $ "Internal error, this should not happen."
insertVar (sig, c:ctxt) i t = 
    case M.lookup i c of
        Just _  -> fail $ 
            "TYPE ERROR\n\nFailed to add " 
            ++ printTree i ++ "to the context, as it is already defined within this block."
        Nothing -> 
            if t == Type_void then
                fail $ "TYPE ERROR\n\nCannot declare variable " ++ printTree i ++ " as void."
            else
                return (sig, (M.insert i t c):ctxt)


newBlock :: Env -> Env
newBlock (sig,ctxt) = (sig, M.empty:ctxt)


emptyEnv :: Env
emptyEnv = (M.fromList 
    [ 
        (Id "printInt",    ([Type_int],    Type_void))
      , (Id "printDouble", ([Type_double], Type_void))
      , (Id "readInt",     ([],            Type_int))
      , (Id "readDouble",  ([],            Type_double))
    ], [M.empty])


buildEnv :: [Def] -> Err Env
buildEnv [] = return emptyEnv
buildEnv (DFun t i arg _:xs) = do
    env <- buildEnv xs
    insertFun env i (map (\(ADecl t _) -> t) arg, t) 


typecheck :: Program -> Err ()
typecheck (PDefs []) = fail $ "TYPE ERROR\n\nFile cannot be empty."
typecheck (PDefs defs) = do
    env <- buildEnv defs
    forM_ defs (checkDef env)


checkDef :: Env -> Def -> Err ()
checkDef env (DFun ty (Id n) args stms) = do
    if (n == "main") then checkMain ty args else ok
    env' <- foldM (\e (ADecl ty' i) -> insertVar e i ty') env args
    foldM_ (\e s -> checkStm e s ty) env' stms


checkMain :: Type -> [Arg] -> Err ()
checkMain Type_int [] = ok
checkMain Type_int xs = fail $ "TYPE ERROR\n\nError, main cannot have arguments."
checkMain ty _ = fail $ typeMismatchError (Id "main") Type_int ty

{- 
In env' <- checkStm env stm ty we have
    env: the current environment
    stm: the stm to be checked for validity
    ty: the return type of the function in which stm appears (needed for SReturn and SReturnVoid)
    env': the updated environment (stm may be variable declaration)
          or an error message (if stm is not valid)
-}
checkStm :: Env -> Stm -> Type -> Err Env 
checkStm env (SExp e) ty = do
    inferTypeExp env e
    return env
checkStm env (SDecls ty' ids) ty =
    foldM (\e i -> insertVar e i ty') env ids
checkStm env (SReturn e) ty = do
    checkExp env e ty
    return env

 checkStm env (SInit ty' i e) ty = do
     env' <- insertVar env i ty'
     ty1 <- inferTypeExp env' e
     if ty1 == ty then
         return env'
    else
        fail $ typeMismatchError e ty ty1
    -- similar to SDecls, but not need for foldM

-- checkStm env SReturnVoid Type_void =
-- the next case is only executed in case ty is not Type_void
-- checkStm env SReturnVoid ty = do
    -- return a typeMismatchError

-- checkStm env (SWhile e stm) ty = do
    -- use newBlock

-- checkStm env (SBlock stms) ty = do
    -- use newBlock
    -- use foldM_ to fold checkStm over all stms

-- checkStm env (SIfElse e stm1 stm2) ty = do
    -- use newBlock in both branches

{-   
Once you have all cases you can delete the next line which is only needed to catch all cases that are not yet implemented.
-}
checkStm _ s _ = fail $ "Missing case in checkStm encountered:\n" ++ printTree s


{- 
In ty <- inferTypExp env e we have
    env: the current environment
    e: the expression 
    ty: the type of e
        or an error message (if we cannot assign a type to e)
-}
inferTypeExp :: Env -> Exp -> Err Type
inferTypeExp env (EInt _) = return Type_int
-- inferTypeExp env (EDouble _) = 
-- inferTypeExp env (EString _) = 
inferTypeExp env (EId i) = do
    ty <- lookupVar i env
    return ty
    -- use lookupVar 
-- inferTypeExp env (EApp i exps) = do
    -- use lookupFun
    -- use forM_ to iterate checkExp over exps
-- inferTypeExp env (EPIncr e) = 
    -- use inferTypeOverloadedExp 
-- inferTypeExp env (EPDecr e) = 
-- inferTypeExp env (EIncr e) = 
-- inferTypeExp env (EDecr e) = 
-- inferTypeExp env (ETimes e1 e2) = 
-- inferTypeExp env (EDiv e1 e2) = 
 inferTypeExp env (EPlus e1 e2) = do
    t1 <- inferTypeExp env e1
    t2 <- inferTypeExp env e2
    if t1 == Type_int && t1 == Type_int then
        return Type_int
    else
        fail $ typeMismatchError (EPlus e1 e2) Type_int Type_int
-- inferTypeExp env (EMinus e1 e2) = 
-- inferTypeExp env (ELt e1 e2) = do
-- inferTypeExp env (EGt e1 e2) = 
-- inferTypeExp env (ELtEq e1 e2) = 
-- inferTypeExp env (EGtEq e1 e2) = 
-- inferTypeExp env (EEq e1 e2) = do
-- inferTypeExp env (ENEq e1 e2) = 
-- inferTypeExp env (EAnd e1 e2) = do
-- inferTypeExp env (EOr e1 e2) = 

inferTypeExp env (EAss e1 e2) = do
    ty <- inferTypeExp env e1
    checkExp env e2 ty
    return ty
inferTypeExp env (ETyped e ty) = do
    checkExp env e ty
    return ty


    
{-
Once you have all cases you can delete the next line which is only needed to catch all cases that are not yet implemented.
-}
inferTypeExp _ e = fail $ "Missing case in inferTypeExp encountered:\n" ++ printTree e


inferTypeOverloadedExp :: Env -> Alternative Type -> Exp -> [Exp] -> Err Type
inferTypeOverloadedExp env (Alternative ts) e es = do
    ty <- inferTypeExp env e
    unless (ty `elem` ts) $ 
        fail $ typeMismatchError e (Alternative ts) ty
    forM_ es (flip (checkExp env) ty)
    return ty


checkExp :: Env -> Exp -> Type -> Err ()
checkExp env e ty = do
    ty' <- inferTypeExp env e
    unless (ty == ty') $ 
        fail $ typeMismatchError e ty ty'