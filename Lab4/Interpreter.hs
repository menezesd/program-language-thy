module Interpreter where

import AbsHSK
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad
import Control.DeepSeq
import ErrM
    

data EvStrat = CallByValue | CallByName
               deriving (Show)


cnvrtStr :: String -> EvStrat
cnvrtStr str = case str of
                 "-n" -> CallByName
                 "-v" -> CallByValue


type Env = (EvStrat, Funs, Var)
emptyEnv :: EvStrat -> Env
emptyEnv evStrat = (evStrat, emptyFuns, emptyVar)

getFuns :: Env -> Funs
getFuns (str, funs, vars) = funs

getStr :: Env -> EvStrat
getStr (str, _, _) = str
    
type Funs = Map Ident Val
emptyFuns :: Funs
emptyFuns = Map.empty

    
type Var = Map Ident Val
emptyVar :: Var
emptyVar = Map.empty

data Val = Cl Ident Exp (Map Ident Val)
         deriving (Show)
                  
                  
lookupVar :: Env -> Ident -> Val
lookupVar (_, funs, vars) id =
    case lookupVar' vars id of
      Just v  -> v
      Nothing -> case lookupFun funs id of
                   Just v -> v
                   Nothing -> error $ (show id) ++ " doesn't exist."


lookupVar' :: Var -> Ident -> Maybe Val
lookupVar' vs id = case (Map.lookup id vs) of
                        Just v -> Just v
                        Nothing -> Nothing


lookupFun :: Funs -> Ident -> Maybe Val
lookupFun funs id = case (Map.lookup id funs) of
                      Just v -> Just v
                      Nothing -> Nothing


update :: Env -> Ident -> Val -> Env
update (st, funs, v) id val = (st, funs, Map.insert id val v)
                                 

collectDefs :: Program -> Env -> Env
collectDefs (Prog []) env = env
collectDefs (Prog ((DDef id ids exp):ds)) (str, funs, vars)
    = collectDefs (Prog ds) (str, Map.insert id (createClosure ids exp) funs, vars)


createClosure :: [Ident] -> Exp -> Val
createClosure (id:[]) e = Cl id e Map.empty
createClosure (id:ids) e = Cl id (expFromVal $ createClosure ids e) (Map.empty)
createClosure [] (EAbs id e) = Cl id e Map.empty
createClosure [] e = Cl (Ident "_") e Map.empty

expFromVal :: Val -> Exp
expFromVal (Cl id exp _) = EAbs id exp
                           
interpret :: Program -> String -> Err Integer
interpret tree str = do
  let globalEnv = collectDefs tree (emptyEnv $ cnvrtStr str)
  case (Map.lookup (Ident "main") (getFuns globalEnv)) of
    Just (Cl _ exp _) -> do
                       res <- eval globalEnv exp
                       res' <- getInt res
                       return res'
    Nothing  -> fail "There is no main function."

getInt :: Val -> Err Integer
getInt (Cl _ (EInt i) _) = return i
getInt v = fail "Tries to return non integer."
  

eval :: Env -> Exp -> Err Val
eval env exp =
    case exp of
      (EVar id)       -> evalVar env id
      (EInt i)        -> evalInt env i
      (EApp e1 e2)    -> evalApp env e1 e2
      (EAdd e1 e2)    -> evalAdd env e1 e2
      (ESub e1 e2)    -> evalSub env e1 e2
      (ELt  e1 e2)    -> evalELt env e1 e2
      (EIf  e1 e2 e3) -> evalIf env e1 e2 e3
      (EAbs id e)     -> evalAbs env id e


evalVar :: Env -> Ident -> Err Val
evalVar (st, funs, vars) id = case lookupVar (st, funs, vars) id of
                                (Cl (Ident "_") e vars') -> eval (st, funs, vars') e
                                (Cl id' exp vars')       -> return (Cl id' exp vars')                   
                   

evalInt :: Env -> Integer -> Err Val
evalInt env i = return $ Cl (Ident "_") (EInt i) Map.empty


evalApp :: Env -> Exp -> Exp -> Err Val
evalApp (str, funs, vars) e1 e2 = do
  (Cl id exp vars') <- eval (str, funs, vars) e1
  case str of
    CallByValue -> do 
             v2 <- eval (str, funs, vars) e2
             eval (update (str, funs, vars') id v2) exp
    CallByName -> do 
             let v2 = Cl (Ident "_") e2 vars
             eval (update (str, funs, vars') id v2) exp

evalAdd :: Env -> Exp -> Exp -> Err Val
evalAdd env e1 e2 = do
  c1 <- eval env e1
  c2 <- eval env e2
  case c1 of
      (Cl _ (EInt i1) _) -> case c2 of
                              (Cl _ (EInt i2) _) -> return (Cl (Ident "_") (EInt (i1 + i2)) Map.empty)
                              _                  -> fail "e2 in ELt is not an Integer in Add" 
      _                  -> fail $ show "e1 in ELt is not an Integer in Add"
                    

evalSub :: Env -> Exp -> Exp -> Err Val
evalSub env e1 e2 = do
  c1 <- eval env e1
  c2 <- eval env e2
  case c1 of
      (Cl _ (EInt i1) _) -> case c2 of
                              (Cl _ (EInt i2) _) -> return (Cl (Ident "_") (EInt (i1 - i2)) Map.empty)
                              _                  -> fail "e2 in ELt is not an Integer in Sub" 
      _                  -> fail $ show "e1 in ELt is not an Integer in Sub" 
    

evalELt :: Env -> Exp -> Exp -> Err Val
evalELt env e1 e2 = do
    (Cl _ e1' var1) <- eval env e1
    (Cl _ e2' var2) <- eval env e2
    c1 <- eval env e1
    c2 <- eval env e2
    case c1 of
      (Cl _ (EInt i1) _) -> case c2 of
                              (Cl _ (EInt i2) _) -> if i1 < i2
                                                    then return (Cl (Ident "_") (EInt 1) Map.empty)
                                                    else return (Cl (Ident "_") (EInt 0) Map.empty)
                              _                  -> fail "e2 in ELt is not an Integer in Lt" 
      _                  -> fail $ show $ "e1 in ELt is not an Integer in Lt" ++ show c1
                            

evalIf :: Env -> Exp -> Exp -> Exp -> Err Val
evalIf env e1 e2 e3 = do
  (Cl _ (EInt i) _) <- eval env e1
  case i of
    1 -> eval env e2
    _ -> eval env e3

                      
evalAbs :: Env -> Ident -> Exp -> Err Val
evalAbs (st, fs, vs) id e = return $ Cl id e vs
                      

          