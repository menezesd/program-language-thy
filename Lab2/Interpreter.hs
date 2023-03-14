module Interpreter where

import AbsCPP
import PrintCPP
import ErrM
import Control.Monad
import Data.Map
import Data.Maybe

type Env = (Funs, [Block])

-- Key is a name of a function and value is a tuple:
-- (names of arguments of the function, statements of the function)
type Funs = Map Id ([Id], [Stm])
    
type Block = Map Id Val

    
msgErrDeclVar = "Variable name not declared."
msgErrDeclFun = "Function name not declared."

                
evalDefs :: Env -> [Def] -> Env
evalDefs env (def:defs) | defs == [] = extendFun env def
                        | otherwise  = evalDefs (extendFun env def) defs
                
interpret :: Program -> IO ()
interpret (PDefs defs) = do
          let globalEnv = evalDefs emptyEnv defs
          result <- evalExp globalEnv (EApp (Id "main") [])
          return ()

-------------------------------------------------------------------------


execStm :: Env -> Stm -> IO (Val, Env)
execStm env stm = case stm of
                    (SExp exp) -> do
                        (val, env') <- evalExp env exp
                        return (VVoid, env') 
                    (SDecls t ids) -> return $ decl env ids'
                        where ids' = zip ids (replicate (length ids) VUndefined)
                              decl :: Env -> [(Id, Val)] -> (Val, Env)
                              decl env' ((id, val):rest) | rest == [] = extendVar env' id val
                                                         | otherwise = extendVar (snd (decl env' rest)) id val
                    (SInit t id exp) -> do
                             (val, env') <- evalExp env exp
                             return $ initVar env' id val

                    (SReturn exp) -> do
                             (val, env') <- evalExp env exp
                             return (val, env')
                    
                    (SWhile exp stm) -> execWhile env exp stm
                        
                    (SBlock stms) -> execBlock (newBlock env) stms
                    
                    (SIfElse exp stm1 stm2) -> do
                             (val, env') <- evalExp env exp
                             case val of
                               VInteger 1 -> execStm env' stm1
                               _          -> execStm env' stm2

                    _ -> return (VVoid, env)
                               

                                           
execBlock :: Env -> [Stm] -> IO (Val, Env)
execBlock env [] = return (VVoid, exitBlock env)
execBlock env ((SReturn exp):_) = do
  (val, env') <- evalExp env exp
  return (val, exitBlock env')
execBlock env (stm:stms) = do
  (val, env') <- execStm env stm
  case val of
    VVoid -> execBlock env' stms
    _     -> return (val, env')


execWhile :: Env -> Exp -> Stm -> IO (Val, Env)
execWhile env exp stm = do
  (val, env') <- evalExp env exp
  case val of
    VInteger 0 -> return (VVoid, env')
    _          -> do
             (val, env'') <- execStm env' stm
             case val of
               VVoid -> do
                        res <- execWhile env'' exp stm
                        return res
               _     -> return (val, env'')
             
 
-------------------------------------------------------------------------                 


evalExp :: Env -> Exp -> IO (Val, Env)
evalExp env exp = case exp of
                    ETrue -> return (VInteger 1, env)
                    EFalse -> return (VInteger 0, env)
                    EInt i -> return (VInteger i, env)
                    EDouble d -> return (VDouble d, env)
                    EId id -> return (lookupVar id env, env)
                    EApp id exps -> evalFun env id exps

                    EPostIncr (EId id) -> return (val, env')
                                         where val = lookupVar id env
                                               (val', env') = case val of
                                                        (VInteger i) ->
                                                            extendVar env id (VInteger (i + 1))
                                                        (VDouble d) ->
                                                            extendVar env id (VDouble (d + 1))
                    EPostDecr (EId id) -> return (val, env')
                                         where val = lookupVar id env
                                               (val', env') = case val of
                                                        (VInteger i) ->
                                                            extendVar env id (VInteger (i - 1))
                                                        (VDouble d) ->
                                                            extendVar env id (VDouble (d - 1))
                    EPreIncr (EId id) -> return $ case val of
                                                  (VInteger i) -> (VInteger (i + 1), env')
                                                  (VDouble d) -> (VDouble (d + 1), env')
                                         where val = lookupVar id env
                                               (val', env') = case val of
                                                        (VInteger i) ->
                                                            extendVar env id (VInteger (i + 1))
                                                        (VDouble i) ->
                                                            extendVar env id (VDouble (i + 1))
                    EPreDecr (EId id) -> return $ case val of
                                                  (VInteger i) -> (VInteger (i - 1), env')
                                                  (VDouble d) -> (VDouble (d - 1), env')
                                         where val = lookupVar id env
                                               (val', env') = case val of
                                                        (VInteger i) ->
                                                               extendVar env id (VInteger (i - 1))
                                                        (VDouble i) ->
                                                               extendVar env id (VDouble (i - 1))
                                                                         
                    ETimes exp1 exp2 -> evalArithm env exp1 exp2 valTimes
                    EDiv   exp1 exp2 -> evalArithm env exp1 exp2 valDiv 
                    EPlus  exp1 exp2 -> evalArithm env exp1 exp2 valPlus 
                    EMinus exp1 exp2 -> evalArithm env exp1 exp2 valMinus
                                        
                    ELt   exp1 exp2 -> evalLogic env exp1 exp2 valLt
                    EGt   exp1 exp2 -> evalLogic env exp1 exp2 valGt
                    ELtEq exp1 exp2 -> evalLogic env exp1 exp2 valLtEq
                    EGtEq exp1 exp2 -> evalLogic env exp1 exp2 valGtEq
                    EEq   exp1 exp2 -> evalLogic env exp1 exp2 valEq
                    ENEq  exp1 exp2 -> evalLogic env exp1 exp2 valNEq
                        
                    EAnd exp1 exp2 -> do
                             (val1, env1) <- evalExp env exp1
                             case val1 of
                               VInteger 0 -> return (VInteger 0, env1)
                               _    -> do
                                        (val2, env2) <- evalExp env1 exp2
                                        return $ (case val2 of
                                                VInteger 0 -> VInteger 0
                                                _          -> VInteger 1
                                                 , env2)
                              
                    EOr exp1 exp2 -> do
                             (val1, env1) <- evalExp env exp1
                             case val1 of
                                      VInteger 1 -> return (VInteger 1, env1)
                                      _    -> do
                                        (val2, env2) <- evalExp env1 exp2
                                        return $ (case val2 of
                                                 VInteger 1 -> VInteger 1
                                                 _          -> VInteger 0
                                                 , env2)
                              
                    EAss exp1 exp2 -> case exp1 of
                                        EId id -> do
                                                  (val, env') <- evalExp env exp2
                                                  let (val'', env'') = extendVar env' id val
                                                  return (val'', env'')
                                        _      ->  do
                                                  (val2, env2) <- evalExp env exp2
                                                  (val1, env1) <- evalExp env2 exp1
                                                  return (val1, env1)




evalArgs :: [(Id, Exp)] -> Env -> IO Env
evalArgs ((id, exp):rest) env = do
  (val, env') <- evalExp env exp
  let (valStep, envStep) = initVar env' id val
  if (null rest) then
    return envStep
  else evalArgs rest envStep
evalArgs _ env = return env
                 

evalFun :: Env -> Id -> [Exp] -> IO (Val, Env)
evalFun env (Id "printInt") [exp] = do
  (val, env') <- evalExp env exp
  putStrLn $ showVal val
  return (VVoid, env')
evalFun env (Id "printDouble") [exp] = do
  (val, env') <- evalExp env exp
  putStrLn $ showVal val
  return (VVoid, env')
evalFun env (Id "readInt") [] = do
  num <- getLine
  return (VInteger (read num :: Integer), env)
evalFun env (Id "readDouble") [] = do
  num <- getLine
  return (VDouble (read num :: Double), env)
evalFun env id exps = do
  let (ids, stms) = lookupFun id env
  envArgs <- evalArgs (zip ids exps) (newBlock env)
  (val, env') <- execBlock envArgs stms
  return (val, env')
                              

evalLogic :: Env -> Exp -> Exp -> (Val -> Val -> Integer) -> IO (Val, Env)
evalLogic env exp1 exp2 op = do
  (val1, env1) <- evalExp env exp1
  (val2, env2) <- evalExp env1 exp2
  return $ case (op val1 val2) of
                  1 -> (VInteger 1, env2)
                  _ -> (VInteger 0, env2)

                       
evalArithm :: Env -> Exp -> Exp -> (Val -> Val -> Val) -> IO (Val, Env)
evalArithm env exp1 exp2 op = do
  (val1, env1) <- evalExp env exp1
  (val2, env2) <- evalExp env1 exp2 
  return (op val1 val2, env2)                   

                      
-------------------------------------------------------------------------


showVal :: Val -> String
showVal val = case val of
                VInteger i -> show i
                VDouble  d -> show d
                VString  s -> show s
                VVoid      -> ""
                VUndefined -> "Undefined"
                                    

valTimes :: Val -> Val -> Val
valTimes (VInteger i1) (VInteger i2) = VInteger (i1 * i2)
valTimes (VDouble d1) (VDouble d2) = VDouble (d1 * d2)
                                       
valDiv :: Val -> Val -> Val
valDiv (VInteger i1) (VInteger i2) = VInteger (i1 `div` i2)
valDiv (VDouble d1) (VDouble d2) = VDouble (d1 / d2)

valPlus :: Val -> Val -> Val
valPlus (VInteger i1) (VInteger i2) = VInteger (i1 + i2)
valPlus (VDouble d1) (VDouble d2) = VDouble (d1 + d2)
valPlus (VString s1) (VString s2) = VString (s1 ++ s2)

valMinus :: Val -> Val -> Val
valMinus (VInteger i1) (VInteger i2) = VInteger (i1 - i2)
valMinus (VDouble d1) (VDouble d2) = VDouble (d1 - d2)

valLt :: Val -> Val -> Integer
valLt (VInteger i1) (VInteger i2) = case (i1 < i2) of
                                      True -> 1
                                      _    -> 0
valLt (VDouble d1) (VDouble d2) = case (d1 < d2) of
                                      True -> 1
                                      _    -> 0

valGt :: Val -> Val -> Integer
valGt (VInteger i1) (VInteger i2) = case (i1 > i2) of
                                      True -> 1
                                      _    -> 0
valGt (VDouble d1) (VDouble d2) = case (d1 > d2) of
                                      True -> 1
                                      _    -> 0

valLtEq :: Val -> Val -> Integer
valLtEq (VInteger i1) (VInteger i2) = case (i1 <= i2) of
                                      True -> 1
                                      _    -> 0
valLtEq (VDouble d1) (VDouble d2) = case (d1 <= d2) of
                                      True -> 1
                                      _    -> 0

valGtEq :: Val -> Val -> Integer
valGtEq (VInteger i1) (VInteger i2) = case (i1 >= i2) of
                                      True -> 1
                                      _    -> 0
valGtEq (VDouble d1) (VDouble d2) = case (d1 >= d2) of
                                      True -> 1
                                      _    -> 0           

valEq :: Val -> Val -> Integer
valEq (VInteger i1) (VInteger i2) = case (i1 == i2) of
                                      True -> 1
                                      _    -> 0
valEq (VDouble d1) (VDouble d2) = case (d1 == d2) of
                                      True -> 1
                                      _    -> 0            

valNEq :: Val -> Val -> Integer
valNEq (VInteger i1) (VInteger i2) = case (i1 /= i2) of
                                      True -> 1
                                      _    -> 0
valNEq (VDouble d1) (VDouble d2) = case (d1 /= d2) of
                                      True -> 1
                                      _    -> 0            


-------------------------------------------------------------------------


           
lookupVar :: Id -> Env -> Val
lookupVar id env =
          let srch = filter (/= Nothing) (map (Map.lookup id) (snd env))
          in case srch  of
            [] -> error $ msgErrDeclVar ++ show env
            _  -> fromJust $ head srch

lookupFun :: Id -> Env -> ([Id], [Stm])
lookupFun id env = 
    case Map.lookup id (fst env) of
        Just f ->  f
        Nothing -> error $ msgErrDeclFun ++ show id

initVar :: Env -> Id -> Val -> (Val, Env)
initVar (funs, (bl:bls)) id val = (VVoid, (funs, Map.insert id val bl : bls))

extendVar :: Env -> Id -> Val -> (Val, Env)
extendVar (funs, (bl:bls)) id VUndefined = (VVoid, (funs, Map.insert id VUndefined bl : bls))
extendVar (funs, (bl:bls)) id val = (val, (funs , extendVar' id val (bl:bls)))

extendVar' :: Id -> Val -> [Block] -> [Block]
extendVar' id val (bl:bls) | Map.lookup id bl /= Nothing = Map.insert id val bl : bls
                           | bls == [] = (Map.insert id val bl) : bls
                           | otherwise = bl : (extendVar' id val bls)             

extendFun :: Env -> Def -> Env
extendFun (funs, blocks) (DFun t id args stms) =
    (Map.insert id ([aid | (ADecl _ aid) <- args] ,stms) funs, blocks)

newBlock :: Env -> Env
newBlock (funs, blocks) = (funs, emptyBlock : blocks)

emptyBlock :: Block
emptyBlock = Map.empty

exitBlock :: Env -> Env
exitBlock (funs, []) = (funs, [])
exitBlock (funs, blocks) = (funs, tail blocks)

emptyEnv :: Env
emptyEnv = (emptyFuns, [emptyBlock])

emptyFuns :: Funs
emptyFuns = Map.empty


         