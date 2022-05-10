{-# LANGUAGE RecordWildCards, FlexibleInstances, FlexibleContexts, PatternSynonyms #-}

module Interpreter ( exec, Value(..), IIO(..), Interpreter(..), emptyEnv ) where

import AbsCPP
import ErrM
import PrintCPP

import Data.Map ( Map )
import qualified Data.Map as M
import Control.Monad.State ( MonadState, StateT, get, put, modify, foldM, liftIO, lift )

-- stores both types (VInt, VDouble, VVoid) and values (Integer or Double)
data Value = VInt Integer
           | VDouble Double
           | VVoid
           | VUndefined deriving Eq
           


pattern VTrue = VInt 1
pattern VFalse = VInt 0
--to interact with a test files?
class MonadState Env i => Interpreter i where
    printInt :: Integer -> i ()
    printDouble :: Double -> i ()
    readInt :: i Integer
    readDouble :: i Double
    getEnv :: i Env
    getEnv = get
    setEnv :: Env -> i ()
    setEnv = put
    modifyEnv :: (Env -> Env) -> i ()
    modifyEnv = modify
    modifyEnv' :: (Env -> i Env) -> i ()
    modifyEnv' f = do
        env <- getEnv
        env' <- f env
        setEnv env'

-- interpreted program runs in the IO monad to interact via the terminal
instance Interpreter (StateT Env IO) where
    printInt i = liftIO $ putStrLn $ show i
    printDouble d = liftIO $ putStrLn $ show d
    readInt = liftIO $ do
        line <- getLine
        return (read line)
    readDouble = liftIO $ do
        line <- getLine
        return (read line)

data IIO = IIO {
    inputs :: [Value]
  , outputs :: [Value]
}

-- used for testing reading test/<filename>.inputs and comparing to test/<filename>.outputs
instance Interpreter (StateT Env (StateT IIO Err)) where
    printInt i = lift $ modify (\io@IIO{..} -> io{outputs = VInt i:outputs}) 
    printDouble d = lift $ modify (\io@IIO{..} -> io{outputs = VDouble d:outputs}) 
    readInt = lift $ do
        IIO{..} <- get
        case inputs of
            (VInt i:_) -> do
                modify (\io@IIO{..} -> io{inputs = tail inputs}) 
                return i
            _ -> fail $ "Invalid input given. expected an int."
    readDouble = lift $ do
        IIO{..} <- get
        case inputs of
            (VDouble d:_) -> do
                modify (\io@IIO{..} -> io{inputs = tail inputs}) 
                return d
            (VInt i:_) -> do
                modify (\io@IIO{..} -> io{inputs = tail inputs}) 
                return $ fromInteger i
            _ -> fail $ "Invalid input given. expected a double."

type Sig = Map Id Def
type Context = Map Id Value
type Env = (Sig, [Context])

emptyEnv :: Env
emptyEnv = (M.empty, [M.empty]) 

extendSig :: Interpreter i => Def -> i ()
extendSig def@(DFun _ i _ _) = modifyEnv $ \(sig,ctxt) -> (M.insert i def sig, ctxt)

lookupSig :: Interpreter i => Id -> i Def
lookupSig i = do
    (sig,_) <- getEnv
    case M.lookup i sig of
        (Just f) -> return f
        Nothing -> fail $ "Error, could not find " ++ printTree i ++ "."

extendContext :: Interpreter i => Id -> Value -> i ()
extendContext i v = modifyEnv $ \(sig, ctxt) -> case ctxt of
    [] -> (sig, [M.insert i v M.empty])
    c:txt -> (sig, M.insert i v c:txt)

updateContext :: Interpreter i => Id -> Value -> i ()
updateContext i v = modifyEnv' $ \(sig, ctxt) -> case ctxt of
    [] -> fail $ "Internal error, " ++ printTree i ++ " could not be found."
    c:txt -> case M.lookup i c of
        (Just _) -> return (sig, M.insert i v c:txt)
        Nothing -> setEnv (sig,txt) >> updateContext i v >> getEnv >>=
            \(_,txt') -> return (sig, c:txt')

lookupContext :: Interpreter i => Id -> i Value
lookupContext i = do
    env@(sig,ctxt) <- getEnv
    case ctxt of
        [] -> fail $ "Error, could not find " ++ printTree i ++ "."
        c:txt -> case M.lookup i c of
            (Just f) -> return f
            Nothing -> setEnv (sig,txt) >> lookupContext i >>= 
                \r -> setEnv env >> return r

push :: Interpreter i => i ()
push = modifyEnv $ \(sig, ctxts) -> (sig, M.empty:ctxts)

pop :: Interpreter i => i ()
pop = modifyEnv' $ \(sig, ctxt) -> case ctxt of
        [] -> fail $ "Internal error, can't pop an empty context."
        (c:txt) -> return (sig, txt)

pushPop :: Interpreter i => i a -> i a-- the first i is
--pushPop f = push >> f >>= \v -> pop >> return v
--pushPop f = push >> ( f >>= ( \v -> (pop >> return v) ) )
pushPop f = do
    push
    v <- f
    pop 
    return v

exec :: Interpreter i => Program -> i ()
exec (PDefs defs) = do
    setEnv emptyEnv
    mapM extendSig defs
    (DFun _ _ _ stms) <- lookupSig (Id "main")
    evalStms stms
    return ()

-- Maybe Value: Use "Just" for SReturn, SReturnVoid, "Nothing" for the other cases. 
evalStms :: Interpreter i => [Stm] -> i (Maybe Value)
evalStms [] = return Nothing
evalStms (s:tms) = do
    v <- evalStm s
    if v == Nothing then evalStms tms
    else return v

evalStm :: Interpreter i => Stm -> i (Maybe Value)
evalStm (SExp e) = do
    evalExp e
    return Nothing
evalStm (SDecls _ ids) = do
    mapM (\i -> extendContext i VUndefined) ids
    return Nothing

evalStm (SInit _ i e) = do
    v<-evalExp e
    extendContext i v
    return Nothing
    
evalStm SReturnVoid = do
    return $ Just VVoid
    
    
    --Just VVoid --VVoid Type_void

evalStm (SReturn e) = do
    v <- evalExp e
    return $ Just v

evalStm (SBlock stms) = pushPop $ evalStms stms  

evalStm (SWhile e stm) = do --use push or push pop to create a new context
    v <- evalExp e
    if v == VTrue then do 
        v <- evalStm stm
        case (v) of
            (Just stm) -> return v 
            (Nothing) -> evalStm (SWhile e stm)
    else return Nothing

        --Return Nothing
    --else return VVoid
    --SWhile e stm
    --v <- evalExp e
    --check if v is true


--goal evaluate e, if it returns true, eval stm

    --check if e is a bool
        --
    --v <- evalStm e
       -- if v == VTrue then pushPop (evalStm stm) >>= \v' -> case v' of
         --   Nothing -> evalStm (SWhile e stm)
           -- Just_ -> return v'
        --else return Nothing
            {--}
evalStm (SIfElse e stm1 stm2) = do
    v <- evalExp e
    if v == VTrue then evalStm stm1
    else evalStm stm2

evalStm stm = 
    fail $ "Missing case in evalStm " ++ printTree stm ++ "\n"

evalExp :: Interpreter i => Exp -> i Value
evalExp ETrue = return VTrue

evalExp EFalse = return VFalse

evalExp (EInt i) = return $ VInt i

evalExp (EDouble d) = return $ VDouble d
    
--evalExp (EString _) = return $ VString
evalExp (EId i) = lookupContext i
    

evalExp (EApp i exps) = do
    vals <- mapM evalExp exps
    case (i, vals) of
        (Id "printInt", [VInt i]) -> do
            printInt i
            return VVoid
        (Id "printInt", _) -> fail $ "Internal error, printInt not supplied with correct arguments."
        (Id "printDouble", [VDouble d]) -> do
            printDouble d
            return VVoid
        (Id "printDouble", _) -> fail $ "Internal error, printDouble not supplied with correct arguments."
        (Id "readInt", []) -> do
            i <- readInt
            return $ VInt i
        (Id "readInt", _) -> fail $ "Internal error, readInt not supplied with correct arguments."
        (Id "readDouble", []) -> do
            d <- readDouble
            return $ VDouble d
        (Id "readDouble", _) -> fail $ "Internal error, readDouble not supplied with correct arguments."
        _ -> do
            (DFun ty _ args stms) <- lookupSig i
            val <- pushPop $ do
                mapM (\(i, v) -> extendContext i v) (zip [i | (ADecl _ i) <- args] vals)
                evalStms stms
            case val of
                Just v -> return v
                Nothing -> 
                    if ty == Type_void then
                        return VVoid
                    else
                        fail $ "Function " ++ printTree i ++ " should return a value."
evalExp (EPIncr e@(EId i)) = do
    val <- evalExp (EId i)
    val' <- addValue val (VInt 1)
    updateContext i val'
    return val
evalExp (EPIncr e) = fail $ "Expected " ++ printTree e ++ " to be an id."

evalExp (EPDecr e@(EId i)) = do
    val <- evalExp (EId i)
    val' <- subValue val (VInt 1)
    updateContext i val'
    return val
    
evalExp (EPDecr e) = fail $ "Expected " ++ printTree e ++ " to be an id."
    
--post inc explained
--a=0
--b=a++
--b gets a which is still 0, and then a is incremented
evalExp (EIncr e@(EId i)) =  do
    val <- evalExp (EId i)
    val' <- addValue val (VInt 1) 
    updateContext i val'
    return val'
evalExp (EIncr e) = fail $ "Expected " ++ printTree e ++ " to be an id."

evalExp (EDecr e@(EId i)) =  do
    val <- evalExp (EId i)
    val' <- subValue val (VInt 1)
    updateContext i val'
    return val'
evalExp (EDecr e) = fail $ "Expected " ++ printTree e ++ " to be an id."
--evalExp (EDecr e) = do



    --evalExp EPDecr e --posdecrement  e--

    {-

    --Ask about the diffrence between pre and post inc, can the same code be used.
    -- How can that code be addapted.

-}


--

evalExp (ETimes e1 e2) = applyFun mulValue e1 e2
evalExp (ELt e1 e2)    = do 
    v1 <- evalExp e1
    v2 <- evalExp e2
    ltValue v1 v2

evalExp (EDiv e1 e2)   = applyFun divValue e1 e2
evalExp (EPlus e1 e2)  = applyFun addValue e1 e2
evalExp (EMinus e1 e2) = applyFun subValue e1 e2


evalExp (EGt e1 e2) = do 
    v1 <- evalExp e1
    v2 <- evalExp e2
    gtValue v1 v2 

    

    
evalExp (ELtEq e1 e2)  = do 
    v1 <- evalExp e1
    v2 <- evalExp e2
    ltEqValue v1 v2

evalExp (EGtEq e1 e2)  = do
    v1 <- evalExp e1
    v2 <- evalExp e2
    gteqValue v1 v2
    

evalExp (EEq e1 e2)    = do
    v1 <- evalExp e1
    v2 <- evalExp e2
    eqValue v1 v2
    
evalExp (ENEq e1 e2) = do
    v1 <- evalExp e1
    v2 <- evalExp e2
    neqValue v1 v2

    
    --check here
evalExp (EAnd e1 e2) = do
    v <- evalExp e1
    if v == VTrue then evalExp e2
    else return VFalse
    
     
evalExp (EOr e1 e2) = do -- is this the correct method or should I write functions(check bottom)
    v <- evalExp e1
    if v == VFalse then evalExp e2
    else return VTrue
{-
evalExp (EAss _ _) = do
    --v <- evalExp (EId i)
    val <- evalExp e2
    updateContext i val
    return val
-}

--evalExp (ETyped _ _) = --what is this for?

evalExp (EAss (EId i) e) = do
    v <- evalExp e
    updateContext i v
    return v

evalExp (EAss _ _) = fail $ "Not given one arg" 

evalExp e = fail $ "Missing case in evalExp." ++ printTree e ++ "\n"


applyFun :: Interpreter i => (Value -> Value -> i Value) -> Exp -> Exp -> i Value
applyFun f e1 e2 = do
    v1 <- evalExp e1
    v2 <- evalExp e2
    f v1 v2

-- computes both the new type (VInt or VDouble) and the new value
addValue :: Interpreter i => Value -> Value -> i Value
addValue (VInt    u) (VInt    v) = return $ VInt $ u + v
addValue (VDouble u) (VDouble v) = return $ VDouble $ u + v
addValue (VDouble u) (VInt    v) = return $ VDouble $ u + (fromInteger v)
addValue (VInt    u) (VDouble v) = return $ VDouble $ (fromInteger u) + v
addValue _ _ = fail $ "Internal error, trying to add incompatible types."


subValue :: Interpreter i => Value -> Value -> i Value
subValue (VInt    u) (VInt    v) = return $ VInt $ u - v
subValue (VDouble u) (VDouble v) = return $ VDouble $ u - v
subValue (VDouble u) (VInt    v) = return $ VDouble $ u - (fromInteger v)
subValue (VInt    u) (VDouble v) = return $ VDouble $ (fromInteger u) - v
subValue _ _ = fail $ "Internal error, trying to sub incompatible types."


mulValue :: Interpreter i => Value -> Value -> i Value
mulValue (VInt    u) (VInt    v) = return $ VInt $ u * v
mulValue (VDouble u) (VDouble v) = return $ VDouble $ u * v
mulValue (VDouble u) (VInt    v) = return $ VDouble $ u * (fromInteger v)
mulValue (VInt    u) (VDouble v) = return $ VDouble $ (fromInteger u) * v
mulValue _ _ = fail $ "Internal error, trying to mul incompatible types."


divValue :: Interpreter i => Value -> Value -> i Value
divValue (VInt    u) (VInt    v) | v /= 0    = return $ VInt $ u `div` v
                                 | otherwise = fail $ "Error division by 0."
divValue (VDouble u) (VDouble v) | v /= 0    = return $ VDouble $ u / v
                                 | otherwise = fail $ "Error division by 0."
divValue (VDouble u) (VInt    v) = divValue (VDouble u) (VDouble $ fromInteger v)
divValue (VInt    u) (VDouble v) = divValue (VDouble $ fromInteger u) (VDouble v)
divValue _ _ = fail $ "Internal error, trying to mul incompatible types."


ltValue :: Interpreter i => Value -> Value -> i Value
ltValue (VInt    u) (VInt    v) | u < v     = return $ VTrue
                                | otherwise = return $ VFalse
ltValue (VDouble u) (VDouble v) | u < v     = return $ VTrue
                                | otherwise = return $ VFalse
ltValue (VDouble u) (VInt    v) = ltValue (VDouble u) (VDouble $ fromInteger v)
ltValue (VInt    u) (VDouble v) = ltValue (VDouble $ fromInteger u) (VDouble v)
ltValue _ _ = fail $ "Internal error, trying to apply ltValue to incompatible types."


--created this fun
ltEqValue :: Interpreter i => Value -> Value -> i Value
ltEqValue (VInt    u) (VInt    v) | u <= v     = return $ VTrue
                                | otherwise = return $ VFalse
ltEqValue (VDouble u) (VDouble v) | u <= v     = return $ VTrue
                                | otherwise = return $ VFalse
ltEqValue (VDouble u) (VInt    v) = ltEqValue (VDouble u) (VDouble $ fromInteger v)
ltEqValue (VInt    u) (VDouble v) = ltEqValue (VDouble $ fromInteger u) (VDouble v)
ltEqValue _ _ = fail $ "Internal error, trying to apply ltValue to incompatible types."


gtValue :: Interpreter i => Value -> Value -> i Value
gtValue (VInt    u) (VInt    v) | u > v     = return $ VTrue
                                | otherwise = return $ VFalse
gtValue (VDouble u) (VDouble v) | u > v     = return $ VTrue
                                | otherwise = return $ VFalse
gtValue (VDouble u) (VInt    v) = gtValue (VDouble u) (VDouble $ fromInteger v)
gtValue (VInt    u) (VDouble v) = gtValue (VDouble $ fromInteger u) (VDouble v)
gtValue _ _ = fail $ "Internal error, trying to apply gtValue to incompatible types."

gteqValue :: Interpreter i => Value -> Value -> i Value
gteqValue (VInt    u) (VInt    v) | u >= v     = return $ VTrue
                                | otherwise = return $ VFalse
gteqValue (VDouble u) (VDouble v) | u >= v     = return $ VTrue
                                | otherwise = return $ VFalse
gteqValue (VDouble u) (VInt    v) = gteqValue (VDouble u) (VDouble $ fromInteger v)
gteqValue (VInt    u) (VDouble v) = gteqValue (VDouble $ fromInteger u) (VDouble v)
gteqValue _ _ = fail $ "Internal error, trying to apply gtValue to incompatible types."

-----------------------------booland----------------------------------

boolAnd :: Interpreter i => Value -> Value -> i Value
boolAnd VFalse _ = return $ VFalse
boolAnd VTrue VTrue = return $ VTrue
boolAnd _ _ = fail $ "Internal error, trying to apply negValue to incompatible types."

----------------------------------------------------------------------

negValue :: Interpreter i => Value -> i Value
negValue VFalse = return $ VTrue
negValue VTrue  = return $ VFalse
negValue _ = fail $ "Internal error, trying to apply negValue to incompatible types."


eqValue :: Interpreter i => Value -> Value -> i Value
eqValue (VInt    u) (VInt    v) | u == v     = return $ VTrue
                                | otherwise = return $ VFalse
eqValue (VDouble u) (VDouble v) | u == v     = return $ VTrue
                                | otherwise = return $ VFalse
eqValue (VDouble u) (VInt    v) = eqValue (VDouble u) (VDouble $ fromInteger v)
eqValue (VInt    u) (VDouble v) = eqValue (VDouble $ fromInteger u) (VDouble v)
eqValue _ _ = fail $ "Internal error, trying to apply ltValue to incompatible types."


neqValue :: Interpreter i => Value -> Value -> i Value
neqValue (VInt    u) (VInt    v) | u == v     = return $ VFalse
                                | otherwise = return $ VTrue
neqValue (VDouble u) (VDouble v) | u == v     = return $ VFalse
                                | otherwise = return $ VTrue
neqValue (VDouble u) (VInt    v) = neqValue (VDouble u) (VDouble $ fromInteger v)
neqValue (VInt    u) (VDouble v) = neqValue (VDouble $ fromInteger u) (VDouble v)
neqValue _ _ = fail $ "Internal error, trying to apply ltValue to incompatible types."
