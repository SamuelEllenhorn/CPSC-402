module TypeChecker ( typecheck ) where

import AbsCPP
import ErrM
import PrintCPP
import Debug.Trace
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
lookupVar i (_,[]) = fail $ "TYPE ERROR\n\n" ++ printTree i ++ " was not declared." -- if you cant find the var in the env
lookupVar i (sig,c:ctxt) = case M.lookup i c of --look if i is in the env
    (Just f) -> return f   --returns a type and a val
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


--int x = x + 1

--return false
checkStm env (SInit ty' i e) ty = do  --sInit Type Id Exp ty' is the pre int check e has ty'
    checkExp env e ty'
    insertVar env i ty'  --insertVar :: Env -> Id -> Type -> Err Env 
    
   --if e2 and ty dont match 
   -- return Type_bool
    
   -- checkExp env e ty'
   -- unless (ty==ty') $
       -- fail $ "types"
    --insertVar env i ty'
    
    --result <- tryJust () $  --try thus if it works do the enxt step, otherwise error out
    --case result of 
        --Left what -> fail "types not compatable'"
        --Right val -> insertVar env i ty'                                  
    --case inferTypeExp env e of   
      -- similar to SDecls, but not need for foldM

-- get the type of e
--if type of e matches ty'
--insertvar env i ty'
--otherwise signal error    
    --checkExp ty' e ty           
    --return Type_bool
     

checkStm env SReturnVoid Type_void = do
    return env
-- the next case is only executed in case ty is not Type_void
checkStm env SReturnVoid ty = do
    -- return a typeMismatchError
    fail $ typeMismatchError SReturnVoid Type_void ty  --typeMismatchError e t1 t2 returns a string 

checkStm env (SWhile e stm) ty = do
    ty <- inferTypeExp env e
    --env1 <- newBlock env
    --env2 <- newBlock env
    if (ty == Type_bool) 
        then do
            let env1 = newBlock env
            checkStm env1 stm ty
            return env
        else
            fail $ "you failed"
    -- use newBlock

checkStm env (SBlock stms) ty = do -- {statement, statment, st}
    let env1 = newBlock env
    --checkStm env1 stms ty --[fold] function
    checker env1 stms
    where
        checker env [] = 
            return env
        checker env (a:as) = do
            newEnv <- checkStm env a ty
            checker newEnv as


    -- use newBlock
    -- use foldM_ to fold checkStm over all stms

checkStm env (SIfElse e stm1 stm2) ty = do
    -- use newBlock in both branches
    --check type of is a bool
    ty <- inferTypeExp env e
    --env1 <- newBlock env
    --env2 <- newBlock env
    if (ty == Type_bool) 
        then do
          --  checkStm env stm1 
            --checkStm env stm2
            --return env 
            let env1 = newBlock env
            let env2 = newBlock env
            checkStm env1 stm1 ty
            checkStm env2 stm2 ty
            return env
             
--checkStm :: Env -> Stm -> Type -> Err Env
            
    else
        fail $ "expression in if statement is not of type bool"
        
        --recursivly check stm1 

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
inferTypeExp env (EInt _) = return Type_int--Are these correct?
inferTypeExp env (EDouble _) = return Type_double
inferTypeExp env (EString _) = return Type_string--Are these Correct?


inferTypeExp env ETrue = return Type_bool

inferTypeExp env EFalse = return Type_bool








inferTypeExp env (EId i) = lookupVar i env       --we want
inferTypeExp env (EPIncr e) = do 
    ty <- inferTypeExp env e
    if (ty == Type_int) -- checkExp env Type_int ty
        then
        return ty --return type of ty
    else
        fail $"error on EPIncr, types dont match"
           --return the inferedtype of lookup  -- lookupVar:   Id -> Env -> Err Type returns a type and exp
    
--EPIncr Exp -- postincrement--EPDecr Exp



    
inferTypeExp env (EApp i exps) = do 
   -- lookupFun :: Env -> Id -> Err FunctionType
   (args, result) <- lookupFun env i
--exps checkExp env ty1
   let f x = checkExp env (fst x) (snd x)
   forM_ (zip exps args) f
   return result
 
   --call checkExp


 --  forM_ exps (lookupFun env i)      --lookupFun :: Env -> Id -> Err FunctionType
     --SInit return env                
    -- use forM_ to iterate checkExp over exps

--inferTypeExp env (EPIncr e) = 
    
    
-- use inferTypeOverloadedExp 
inferTypeExp env (EPDecr e) =  do
    ty <- inferTypeExp env e
    if (ty == Type_int) -- checkExp env Type_int ty
        then
        return ty --return type of ty
    else
        fail $"error on EPDecr, types dont match"



 --    fty <- lookupFun env id
  --   return Type_void
    --aty <- inferTypeExp env arg
    --if (aty == Type_int) 
    --Env -> Exp -> Err Type
    --check exp: checkExp :: Env -> Exp -> Type -> Err ()
inferTypeExp env (EIncr e) = do
    ty <- inferTypeExp env e
    if (ty == Type_int) -- checkExp env Type_int ty
        then
        return ty --return type of ty
    else
        fail $"error on EIncr, types dont match"
    
inferTypeExp env (EDecr e) = do
    ty <- inferTypeExp env e
    if (ty == Type_int) -- checkExp env Type_int ty
        then
        return ty --return type of ty
    else
        fail $"error on EDecr, types dont match"

inferTypeExp env (ETimes e1 e2) = do
    --only works with int or double
    ty <- inferTypeExp env e1
    checkExp env e2 ty          --if e2 and ty dont match 
    -- check if one is in or double
    if (Type_double == ty || Type_int == ty)
        then
        return ty --return type of ty
    else
        fail $"error on multiplication, types dont match"
inferTypeExp env (EDiv e1 e2) = do --- check this one!!!!!!!!!!!!
    --only works with int or double
    ty <- inferTypeExp env e1
    checkExp env e2 ty          --if e2 and ty dont match 
    -- check if one is in or double
    if (Type_double == ty || Type_int == ty)
        then
        return ty --return type of ty
    else
        fail $"error on division, types dont match"


inferTypeExp env (EPlus e1 e2) = do
    --only works with int or double
    ty <- inferTypeExp env e1
    checkExp env e2 ty          --if e2 and ty dont match 
    -- check if one is in or double
    if (Type_double == ty || Type_int == ty || Type_string == ty)
        then
        return ty --return type of ty
    else
        fail $"error on addition, types dont match"


inferTypeExp env (EMinus e1 e2) = do
    --only works with int or double
    ty <- inferTypeExp env e1
    checkExp env e2 ty          --if e2 and ty dont match 
    -- check if one is in or double
    if (Type_double == ty || Type_int == ty)
        then
        return ty --return type of ty
    else
        fail $"error on subtraction, types dont match"

    --Q1 
inferTypeExp env (ELt e1 e2) = do 
    ty <- inferTypeExp env e1
    checkExp env e2 ty          --if e2 and ty dont match 
    return Type_bool
    ---type mismatch error returns a string and takes in e, t1, and t2, turns them into strings concatonates them  
    ---should i create a diffrent function which takes in a lisrt of 
    --if tel = number_types && te2 number_types then
      --  Type_bool
    --else 
      --  fail $ typeMismatchError
    --where
      --  te1 = inferTypeExp e1
  --      te2 = inferTypeExp e2
inferTypeExp env (EGt e1 e2) = do
    ty <- inferTypeExp env e1
    checkExp env e2 ty          --if e2 and ty dont match 
    return Type_bool
inferTypeExp env (ELtEq e1 e2) = do
    ty <- inferTypeExp env e1
    checkExp env e2 ty          --if e2 and ty dont match 
    return Type_bool
inferTypeExp env (EGtEq e1 e2) = do
    ty <- inferTypeExp env e1
    checkExp env e2 ty          --if e2 and ty dont match 
    return Type_bool

inferTypeExp env (EEq e1 e2) = do
     
    ty <- inferTypeExp env e1
    checkExp env e2 ty          --if e2 and ty dont match 
    return Type_bool

inferTypeExp env (ENEq e1 e2) = do
    ty <- inferTypeExp env e1
    checkExp env e2 ty          --if e2 and ty dont match 
    return Type_bool
inferTypeExp env (EAnd e1 e2) = do
    ty <- inferTypeExp env e1
    checkExp env e2 ty          --if e2 and ty dont match 
    return Type_bool
inferTypeExp env (EOr e1 e2) = do --edited
    ty <- inferTypeExp env e1
    checkExp env e2 ty          --if e2 and ty dont match 
    return Type_bool
    --checkStm inferTypeExp e1 inferTypeExp e2

inferTypeExp env (EAss e1 e2) = do
    ty <- inferTypeExp env e1
    checkExp env e2 ty          --if e2 and ty dont match 
    return ty
inferTypeExp env (ETyped e ty) = do
    checkExp env e ty
    return ty

--inferTypeExp env (EFunc id arg) =  do
  --  fty <- lookupFun env id
    --aty <- inferTypeExp env arg
    --if (aty == Type_int)
      --  then
        
        --return fty --return type of ty
    --else
        --fail $"error on addition, types dont match" 
         


--lookupFun :: Env -> Id -> Err FunctionType


    
{-
Once you have all cases you can delete the next line which is only needed to catch all cases that are not yet implemented.
-}
inferTypeExp _ e = fail $ "Missing case in inferTypeExp encountered:\n" ++ show e


inferTypeOverloadedExp :: Env -> Alternative Type -> Exp -> [Exp] -> Err Type
inferTypeOverloadedExp env (Alternative ts) e es = do
    ty <- inferTypeExp env e
    unless (ty `elem` ts) $ 
        fail $ typeMismatchError e (Alternative ts) ty
    forM_ es (flip (checkExp env) ty)
    return ty


checkExp :: Env -> Exp -> Type -> Err ()  --checks through env to obtain exp decideds if theres a type mismatch
checkExp env e ty = do
    ty' <- inferTypeExp env e
    unless (ty == ty') $ 
        fail $ typeMismatchError e ty ty'
