module TypeChecker
       (typecheck) where

import AbsCPP
import PrintCPP
import ErrM
import Control.Monad
import Data.Maybe

import Data.Map (Map)
import qualified Data.Map as Map


--------------------------------------------------------------------------------


-- functions and context stack
type Env = (Sig, [Context])

-- function type signature
type Sig = Map Id ([Type], Type)

-- variables with their types
type Context = Map Id Type


--------------------------------------------------------------------------------
    

lookupVar :: Env -> Id -> Err Type
lookupVar env vid = let srch = filter (/= Nothing)
                               (map (Map.lookup vid) (snd env)) in
                       case srch  of
                             [] -> fail $ "variable name not declared"
                                   ++ "in current block: " ++ show vid
                             _  -> return $ fromJust $ head srch
              

lookupFun :: Env -> Id -> [Exp] -> Err ([Type], Type)
lookupFun env fid exps = 
    case Map.lookup fid (fst env) of
        Just funtyp -> do
             if (length (fst funtyp) /= length exps) then
                fail "Number of arguements"
             else
                return funtyp
        Nothing -> do fail $ "function name not declared: " ++ show fid
                               ++ "-------------"

 
updateVar :: Env -> Id -> Type -> Err Env
updateVar (sig, topctx : restctxs) v typ = 
    if Map.member v topctx then
        fail "variable already declared in current block"
        else
            return (sig, Map.insert v typ topctx : restctxs)

updateFun :: Env -> Id -> ([Type],Type) -> Err Env
updateFun (sig, ctxs) f typ = 
    if Map.member f sig then
        fail "function already declared"
        else
                return (Map.insert f typ sig, ctxs) 


newBlock :: Env -> Env
newBlock (sig, ctxs) = (sig, emptyContext:ctxs)

emptyEnv :: Env
emptyEnv = (emptySig, [emptyContext])

emptySig :: Sig
emptySig = Map.empty

emptyContext :: Context
emptyContext = Map.empty


--------------------------------------------------------------------------------


typecheck :: Program -> Err ()
typecheck (PDefs defs) = do
          builtenv <- foldM
             (\env (id, typs) -> updateFun env id typs)
             emptyEnv
             [
              (Id "printInt", ([Type_int], Type_void)),
              (Id "printDouble", ([Type_double], Type_void)),
              (Id "readInt", ([], Type_int)),
              (Id "readDouble", ([], Type_double))
             ]
             
          globalenv <- foldM
             (\env (DFun typ id args stms) -> updateFun env id
                                              ([Type_void
                                                |_ <- [1..(length args)]]
                                              , typ))
             builtenv
             defs

          
          
          mapM
                (\(DFun outtyp id args stms)  ->
                   let
                        retType = case outtyp of
                                Type_void -> Nothing
                                _ -> Just outtyp
                        in do
                           
                           fbdyenv <-
                                   foldM
                                        (\env (ADecl atyp aid) ->
                                              updateVar env aid atyp
                                         )
                                         (newBlock globalenv)
                                         args
                      
                           typecheckStms fbdyenv retType stms
                )
                defs
          return ()


--------------------------------------------------------------------------------
                 
                 
typecheckStms :: Env -> Maybe Type -> [Stm] -> Err Env
typecheckStms env Nothing [SReturn exp] = do
                    t <- inferExp env exp
                    case t of
                         Type_void -> return env
                         _         -> fail "Return void"
                                        
typecheckStms env (Just typ) (stm:stms) = case stm of
              SExp exp -> do
                   inferExp env exp
                   typecheckStms env (Just typ) stms

              SDecls type' ids -> do
                     res_env <- foldM
                            (\env' id -> updateVar env' id type')
                            env
                            ids
                     typecheckStms res_env (Just typ) stms

              SWhile exp stm' -> do
                     typecheckExp env Type_bool exp
                     typecheckStms (newBlock env) (Just typ) [stm']
                     typecheckStms env (Just typ) stms

              SReturn exp -> do
                      t <- typecheckExp env typ exp
                      if (t /= typ) then
                         fail "Return different type"
                      else return emptyEnv

              SInit type' id exp -> do
                    t <- typecheckExp env type' exp
                    if (t == type') then
                       do
                                resenv <- updateVar env id type'
                                typecheckStms resenv (Just typ) stms
                    else
                       fail $ "SInit error " ++ show id
                    
                    
              SBlock s -> do
                     typecheckStms (newBlock env) (Just typ) s
                     typecheckStms env (Just typ) stms

              SIfElse exp stm1 stm2 -> do
                      typecheckExp env Type_bool exp
                      typecheckStms (newBlock env) (Just typ) [stm1]
                      typecheckStms (newBlock env) (Just typ) [stm2]
                      typecheckStms env (Just typ) stms
                                                                               
typecheckStms _ _ _ = return emptyEnv
                      
                       
typecheckExp :: Env -> Type -> Exp -> Err Type
typecheckExp env typ exp = do
             typ2 <- inferExp env exp
             if (typ2 == typ) then
                return typ2
             else
                fail $ "type of " ++ printTree exp


--------------------------------------------------------------------------------

                     
inferExp :: Env -> Exp -> Err Type
inferExp env x = case x of
         ETrue   -> return Type_bool
         EFalse  -> return Type_bool
         EInt n  -> return Type_int
         EDouble d -> return Type_double
         
         EId id  -> (lookupVar env id)
         EApp id exps -> inferApp env id exps
         EPostIncr a -> inferIncr env a 
         EPostDecr a -> inferIncr env a 
         EPreIncr a -> inferIncr env a 
         EPreDecr a -> inferIncr env a 
         ETimes exp0 exp -> inferArithmBin env exp0 exp
         EDiv exp0 exp -> inferArithmBin env exp0 exp
         EPlus exp0 exp -> inferArithmBin env exp0 exp
         EMinus exp0 exp -> inferArithmBin env exp0 exp
         ELt exp0 exp -> inferBoolBin env exp0 exp
         EGt exp0 exp -> inferBoolBin env exp0 exp
         ELtEq exp0 exp -> inferBoolBin env exp0 exp
         EGtEq exp0 exp -> inferBoolBin env exp0 exp
         EEq exp0 exp -> inferBoolBin env exp0 exp
         ENEq exp0 exp -> inferBoolBin env exp0 exp
         EAnd exp0 exp -> inferBoolBin env exp0 exp
         EOr exp0 exp -> inferBoolBin env exp0 exp
         EAss a b -> do
              typa <- inferExp env a
              typb <- inferExp env b
              if (typa == typb) then
                 return typa
              else
                 fail $ "type of " ++ printTree a
         _ -> fail "Unknown expression"

              
inferArithmBin :: Env -> Exp -> Exp -> Err Type
inferArithmBin env a b = do
    typ <- inferExp env a
    if elem typ [Type_int, Type_double] then do
        typecheckExp env typ b
      else
        fail $ "type of expression " ++ printTree a

             
inferBoolBin :: Env -> Exp -> Exp -> Err Type
inferBoolBin env a b = do
    typa <- inferExp env a
    typb <- inferExp env b
    if (typa == typb) then do
        return Type_bool
    else
        fail $ "type of expression " ++ printTree a

             
inferApp :: Env -> Id -> [Exp] -> Err Type
inferApp env id exps = do
         tapp <- lookupFun env id exps
         return $ snd tapp

                
inferIncr :: Env -> Exp -> Err Type
inferIncr env a = do
          type' <- inferExp env a
          if (type' == Type_bool) then
             fail $ "type of expression " ++ printTree a
          else
             return type'