module CodeGenerator
    (generateCode) where

import AbsCPP
import PrintCPP
import ErrM
import Control.Monad
import Data.Maybe

import Data.Map (Map)
import qualified Data.Map as Map


--------------------------------------------------------------------------------


type Env = ([Label], Addr, [Storage], Funs, String, Integer)
emptyEnv :: String -> Env
emptyEnv className = ([0], 0, [emptyStorage], emptyFuns, className, 0)

getClassName :: Env -> String
getClassName (_, _, _, _, className, _) = className

getAddr :: Env -> Addr
getAddr (_, addr, _, _, _, _) = addr

getStack :: Env -> Integer
getStack (_, _, _, _, _, st) = st

enlargeStack :: Env -> Integer -> Env
enlargeStack (ls, addr, strg, fs, cn, st) i = (ls, addr, strg, fs, cn, st + i)


type Storage = Map Id Addr
emptyStorage :: Storage
emptyStorage = Map.empty


type Funs = Map Id FunType
type FunType = (Type, Id, [Arg])
emptyFuns :: Funs
emptyFuns = Map.empty


type Label = Integer
type Code = String
type Addr = Integer


data Instr = Mul | Add | Div | Sub | PushInt Integer
           | Load Integer | Store Integer | Pop
           | IfEq String | GoTo String | Label String
           | IReturn | DReturn | VReturn | IConst0
           | CmpLt String | CmpGt String | CmpLe String
           | CmpGe String | CmpEq String | CmpNe String 

instance Show Instr where
    show instr = case instr of
                   Mul           -> "   imul" ++ "\n"
                   Div           -> "   idiv" ++ "\n"
                   Add           -> "   iadd" ++ "\n"
                   Sub           -> "   isub" ++ "\n"
                   (PushInt i)   -> "   ldc " ++ (show i) ++ "\n"
                   (Load addr)   -> "   iload " ++ (show addr) ++ "\n"
                   (Store addr)  -> "   istore " ++ (show addr) ++ "\n"
                   Pop           -> "   pop \n"
                   (IfEq label)  -> "   ifeq " ++ label ++ "\n"
                   (GoTo label)  -> "   goto " ++ label ++ "\n"
                   (Label label) -> label ++ ":\n"
                   IReturn       -> "   ireturn" ++ "\n"
                   DReturn       -> "   dreturn" ++ "\n"
                   VReturn       -> "   return" ++ "\n"
                   IConst0       -> "   iconst_0" ++ "\n"
                   (CmpLt label) -> "   if_icmplt " ++ label ++ "\n"
                   (CmpGt label) -> "   if_icmpgt " ++ label ++ "\n"
                   (CmpLe label) -> "   if_icmple " ++ label ++ "\n"
                   (CmpGe label) -> "   if_icmpge " ++ label ++ "\n"
                   (CmpEq label) -> "   if_icmpeq " ++ label ++ "\n"
                   (CmpNe label) -> "   if_icmpne " ++ label ++ "\n"
                                    


--------------------------------------------------------------------------------


newBlock :: Env -> Env
newBlock (ls, addr, strgs, fs, cn, st) = (ls, addr, emptyStorage:strgs, fs, cn, st)

                                 
exitBlock :: Env -> Env
exitBlock (ls, addr, st:strgs, fs, cn, stk) = (ls, addr, strgs, fs, cn, stk)


newLabel :: Env -> (Label, Env)
newLabel (l:ls, addr, strg, fs, cn, st) = (l+1, ((l+1):ls, addr, strg, fs, cn, st))


lookupVar :: Env -> Id -> Maybe Addr
lookupVar (ls, addr, [], fs, cn, st) id = Nothing
lookupVar (ls, addr, addrStrg:rest, fs, cn, st) id =
    case Map.lookup id addrStrg of
      Just adr -> Just adr
      Nothing   -> lookupVar (ls, addr, rest, fs, cn, st) id


lookupFun :: Env -> Id -> Maybe FunType
lookupFun (_, _, _, fs, cn, st) id = Map.lookup id fs


extendVar :: Env -> Id -> Env
extendVar (ls, addr, addrStrg:rest, fs, cn, st) id = (ls, addr+1, updStrg, fs, cn, st)
    where updStrg = (Map.insert id addr addrStrg):rest


extendFun :: Env -> Def -> Env
extendFun (ls, a, s, funs, cn, st) (DFun t id args _) =
    (ls, a, s, Map.insert id (t, id, args) funs, cn, st)

                             
--------------------------------------------------------------------------------

            
                              
generateCode :: Program -> String -> Code
generateCode (PDefs defs) className = (boilerplate className) ++ (concatMap (compileFun env) defs)
    where env = collectFuns (emptyEnv className) defs


collectFuns :: Env -> [Def] -> Env
collectFuns env []     = env
collectFuns env (d:ds) = collectFuns (extendFun env d) ds 


boilerplate :: String -> String
boilerplate className = ".class public " ++ className ++ "\n"
                        ++ ".super java/lang/Object\n\n"
                        ++ ".method public <init>()V\n"
                        ++ "   aload_0\n"
                        ++ "   invokespecial java/lang/Object/<init>()V\n"
                        ++ "   return\n"
                        ++ ".end method\n\n"
                        ++ ";; The java-style main method calls the cc main\n"
                        ++ ".method public static main([Ljava/lang/String;)V\n"
                        ++ "   .limit locals 1\n"
                        ++ "   invokestatic " ++ className ++ "/main()I\n"
                        ++ "   pop\n"
                        ++ "   return\n"
                        ++ ".end method\n\n"
                        ++ ";; Program\n\n" 
                                      

compileFun :: Env -> Def -> Code
compileFun env (DFun _ (Id "main" ) _ stms) =
    ".method public static main()I\n\n"
    ++ "   .limit locals " ++ (show $ getAddr env') ++ "\n"
    ++ "   .limit stack " ++ (show $ getStack env') ++ "\n"
    ++ addReturn code Type_int
    ++ ".end method\n\n"
        where (code, env') = compileStms env stms


compileFun env (DFun t (Id id) args stms) =
    ".method public static " ++ id ++ "(" ++ targs ++ ")" ++ t' ++"\n"
    ++ "   .limit locals " ++ (show $ getAddr env'') ++ "\n"
    ++ "   .limit stack " ++ (show $ getStack env'') ++ "\n"
    ++ addReturn code t
    ++ ".end method\n\n"
        where (code, env'') = compileStms env' stms
              t'     = typeToLetter t
              targs  = argsToString args
              env'   = extendArgs env args


extendArgs :: Env -> [Arg] -> Env
extendArgs env [] = env
extendArgs env ((ADecl t id):rest) = extendArgs (extendVar env id) rest

                      
typeToLetter :: Type -> String
typeToLetter t = case t of
                   Type_bool   -> "I"
                   Type_int    -> "I"
                   Type_double -> "D"
                   Type_void   -> "V"


argsToString :: [Arg] -> String
argsToString args = concatMap (\(ADecl t _) -> typeToLetter t) args


addReturn :: String -> Type -> String
addReturn code t = case last (lines code) of
                   "ireturn" -> code
                   "return"  -> code
                   _         -> case t of
                                  Type_int -> code ++ "ireturn\n"
                                  Type_void -> code ++ "return\n"

--------------------------------------------------------------------------------


compileStms :: Env -> [Stm] -> (Code, Env)
compileStms env [] = ("\n", env)
compileStms env (stm:stms) = (code, env'')
    where (code', env') = compileStm env stm
          (code'', env'') = compileStms env' stms
          code = "\n" ++ code' ++ code''


compileStm :: Env -> Stm -> (Code, Env)
compileStm env stm =
    case stm of
      (SExp (EAss exp1 exp2)) -> compileStmAss env exp1 exp2
      (SExp exp)              -> compileExp env exp
      (SDecls t ids)          -> compileDecl env ids
      (SInit t id exp)        -> compileStm (extendVar env id) (SExp (EAss (EId id) exp))
      (SBlock stms)           -> compileBlock (newBlock env) stms
      (SWhile exp stm)        -> compileWhile env exp stm
      (SIfElse exp stm1 stm2) -> compileIf env exp stm1 stm2
      (SReturn exp)           -> compileReturn env exp
      

compileStmAss :: Env -> Exp -> Exp -> (Code, Env)
compileStmAss env (EId id) e2 =
    case (lookupVar env id) of
      Just addr -> (code, env2)
          where (code2, env2) = compileExp env e2
                codeStore = show $ Store addr
                code = code2 ++ codeStore
      Nothing   -> ("", env)
                                  

compileDecl :: Env -> [Id] -> (Code, Env)
compileDecl env [] = ("", env)
compileDecl env (id:ids) = ("", env'')
    where (code, env'') = compileDecl env' ids
          env' = extendVar env id
                                                  

compileBlock :: Env -> [Stm] -> (Code, Env)
compileBlock  env [] = ("", exitBlock env)
compileBlock  env (stm:stms) = (code, env2)
    where (code1, env1) = compileStm env stm
          (code2, env2) = compileBlock env1 stms
          code = code1 ++ code2


compileWhile :: Env -> Exp -> Stm -> (Code, Env)
compileWhile env exp stm = (code, exitBlock env4)
    where (test, env1) = newLabel env
          testLabel = "l" ++ (show test)
          (end, env2) = newLabel env1
          endLabel = "l" ++ (show end)
          (code1, env3) = compileExp env2 exp
          (code2, env4) = compileStm (newBlock env3) stm
          code = show (Label testLabel) ++
                 code1 ++
                 show (IfEq endLabel) ++
                 code2 ++
                 show (GoTo testLabel) ++
                 show (Label endLabel)


compileIf :: Env -> Exp -> Stm -> Stm -> (Code, Env)
compileIf env exp stm1 stm2 = (code, env5)
    where (tr, env1) = newLabel env
          trLabel = "l" ++ (show tr)
          (fls, env2) = newLabel env1
          flsLabel = "l" ++ (show fls)
          (code1, env3) = compileExp env2 exp
          (code2, env4) = compileStm env3 stm1
          (code3, env5) = compileStm env4 stm2
          code = code1 ++
                 show (IfEq flsLabel) ++
                 code2 ++
                 show (GoTo trLabel) ++
                 show (Label flsLabel) ++
                 code3 ++
                 show (Label trLabel)

                 
compileReturn :: Env -> Exp -> (Code, Env)
compileReturn env exp = (code, env')
    where (code', env') = compileExp env exp
          code = code' ++ (show IReturn)


--------------------------------------------------------------------------------


compileExp :: Env -> Exp -> (Code, Env)
compileExp env exp = case exp of
                       ETimes exp1 exp2 -> compileArithm env exp1 exp2 Mul
                       EPlus  exp1 exp2 -> compileArithm env exp1 exp2 Add
                       EMinus exp1 exp2 -> compileArithm env exp1 exp2 Sub
                       EDiv   exp1 exp2 -> compileArithm env exp1 exp2 Div

                       EInt i -> (show (PushInt i), (enlargeStack env 1))

                       EId id -> compileExpId env id

                       EAss e1 e2 -> compileExpAss env e1 e2

                       ETrue  -> (show (PushInt 1), (enlargeStack env 1))
                       EFalse -> (show (PushInt 0), (enlargeStack env 1))

                       EApp id exps -> compileExpApp env id exps

                       EPostIncr exp -> compileExpPostIncr env exp
                       EPostDecr exp -> compileExpPostDecr env exp
                       EPreIncr  exp -> compileExpPreIncr  env exp
                       EPreDecr  exp -> compileExpPreDecr  env exp

                       ELt   exp1 exp2 -> compileExpLt   env exp1 exp2
                       EGt   exp1 exp2 -> compileExpGt   env exp1 exp2
                       ELtEq exp1 exp2 -> compileExpLtEq env exp1 exp2
                       EGtEq exp1 exp2 -> compileExpGtEq env exp1 exp2
                       EEq   exp1 exp2 -> compileExpEq   env exp1 exp2
                       ENEq  exp1 exp2 -> compileExpNEq  env exp1 exp2
                       EAnd  exp1 exp2 -> compileExpAnd  env exp1 exp2
                       EOr   exp1 exp2 -> compileExpOr   env exp1 exp2
                       

compileArithm :: Env -> Exp -> Exp -> Instr -> (Code, Env)
compileArithm env exp1 exp2 instr = (code, env2)
    where (code1, env1) = compileExp env exp1
          (code2, env2) = compileExp env1 exp2
          code = code1 ++
                 code2 ++
                 (show instr)


compileExpId :: Env -> Id -> (Code, Env)
compileExpId env id =
    case (lookupVar env id) of
      Just addr -> (show (Load addr), (enlargeStack env 1))
      Nothing   -> ("", env)
                   
                 
compileExpAss :: Env -> Exp -> Exp -> (Code, Env)
compileExpAss env (EId id) exp2 =
    case (lookupVar env id) of
      Just addr -> (code, (enlargeStack env2 2))
          where (code2, env2) = compileExp env exp2
                codeStore = show $ Store addr
                codeLoad  = show $ Load addr
                code = code2 ++ codeStore ++ codeLoad
      Nothing   -> ("", env)



compileExpApp :: Env -> Id -> [Exp] -> (Code, Env)
compileExpApp env (Id "printInt") exps = (code, env')
    where (code', env') = compileExps env exps
          code'' = "   invokestatic runtime/printInt(I)V\n"
          code   = code' ++ code''
compileExpApp env (Id "readInt") _ =
    ("   invokestatic runtime/readInt()I\n", env)
compileExpApp env (Id id) exps = 
    case (lookupFun env (Id id)) of
      Just (t, _, args) -> (code, env')
          where (code', env') = compileExps env exps
                code'' = "   invokestatic "
                         ++ (getClassName env) ++ "/" ++ id
                         ++ "(" ++ targs ++ ")" ++ t' ++"\n"
                code   = code' ++ code''
                t'     = typeToLetter t
                targs  = argsToString args
      Nothing           -> ("", env)
    

compileExps :: Env -> [Exp] -> (Code, Env)
compileExps env [] = ("", env)
compileExps env (e:es) = (code, env'')
    where (code', env') = compileExp env e
          (code'', env'') = compileExps env' es
          code = code' ++ code''
                 

compileExpPostIncr :: Env -> Exp -> (Code, Env)
compileExpPostIncr env (EId id) =
    case (lookupVar env id) of
      Just addr -> (code, (enlargeStack env 3))
          where code = show (Load addr)  ++
                       show (Load addr)  ++
                       show (PushInt 1)  ++
                       show Add          ++
                       show (Store addr)
      Nothing   -> ("", env)             


compileExpPostDecr :: Env -> Exp -> (Code, Env)
compileExpPostDecr env (EId id) =
    case (lookupVar env id) of
      Just addr -> (code, (enlargeStack env 3))
          where code = show (Load addr)  ++
                       show (Load addr)  ++
                       show (PushInt 1)  ++
                       show Sub          ++
                       show (Store addr)
      Nothing   -> ("", env)


compileExpPreIncr :: Env -> Exp -> (Code, Env)
compileExpPreIncr env (EId id)=
    case (lookupVar env id) of
      Just addr -> (code, (enlargeStack env 3))
          where code = show (Load addr)  ++
                       show (PushInt 1)  ++
                       show Add          ++
                       show (Store addr) ++
                       show (Load addr)
      Nothing   -> ("", env) 


compileExpPreDecr :: Env -> Exp -> (Code, Env)
compileExpPreDecr env (EId id) =
    case (lookupVar env id) of
      Just addr -> (code, (enlargeStack env 3))
          where code = show (Load addr)  ++
                       show (PushInt 1)  ++
                       show Sub          ++
                       show (Store addr) ++
                       show (Load addr)
      Nothing   -> ("", env) 


compileExpLt :: Env -> Exp -> Exp -> (Code, Env)
compileExpLt env exp1 exp2 = (code, (enlargeStack env3 2))
    where (code1, env1) = compileExp env exp1
          (code2, env2) = compileExp env1 exp2
          (tr, env3) = newLabel env2
          trLbl = "l" ++ (show tr)
          code = show (PushInt 1)   ++
                 code1              ++
                 code2              ++
                 show (CmpLt trLbl) ++
                 show Pop           ++
                 show (PushInt 0)   ++
                 show (Label trLbl) 


compileExpGt :: Env -> Exp -> Exp -> (Code, Env)
compileExpGt   env exp1 exp2 = (code, (enlargeStack env3 2))
    where (code1, env1) = compileExp env exp1
          (code2, env2) = compileExp env1 exp2
          (tr, env3) = newLabel env2
          trLbl = "l" ++ (show tr)
          code = show (PushInt 1)   ++
                 code1              ++
                 code2              ++
                 show (CmpGt trLbl) ++
                 show Pop           ++
                 show (PushInt 0)   ++
                 show (Label trLbl) 


compileExpLtEq :: Env -> Exp -> Exp -> (Code, Env)
compileExpLtEq env exp1 exp2 = (code, (enlargeStack env3 2))
    where (code1, env1) = compileExp env exp1
          (code2, env2) = compileExp env1 exp2
          (tr, env3) = newLabel env2
          trLbl = "l" ++ (show tr)
          code = show (PushInt 1)   ++
                 code1              ++
                 code2              ++
                 show (CmpLe trLbl) ++
                 show Pop           ++
                 show (PushInt 0)   ++
                 show (Label trLbl) 


compileExpGtEq :: Env -> Exp -> Exp -> (Code, Env)
compileExpGtEq env exp1 exp2 = (code, (enlargeStack env3 2))
    where (code1, env1) = compileExp env exp1
          (code2, env2) = compileExp env1 exp2
          (tr, env3) = newLabel env2
          trLbl = "l" ++ (show tr)
          code = show (PushInt 1)   ++
                 code1              ++
                 code2              ++
                 show (CmpGe trLbl) ++
                 show Pop           ++
                 show (PushInt 0)   ++
                 show (Label trLbl) 


compileExpEq :: Env -> Exp -> Exp -> (Code, Env)
compileExpEq   env exp1 exp2 = (code, (enlargeStack env3 2))
    where (code1, env1) = compileExp env exp1
          (code2, env2) = compileExp env1 exp2
          (tr, env3) = newLabel env2
          trLbl = "l" ++ (show tr)
          code = show (PushInt 1)   ++
                 code1              ++
                 code2              ++
                 show (CmpEq trLbl) ++
                 show Pop           ++
                 show (PushInt 0)   ++
                 show (Label trLbl) 


compileExpNEq :: Env -> Exp -> Exp -> (Code, Env)
compileExpNEq  env exp1 exp2 = (code, (enlargeStack env3 2))
    where (code1, env1) = compileExp env exp1
          (code2, env2) = compileExp env1 exp2
          (tr, env3) = newLabel env2
          trLbl = "l" ++ (show tr)
          code = show (PushInt 1)   ++
                 code1              ++
                 code2              ++
                 show (CmpNe trLbl) ++
                 show Pop           ++
                 show (PushInt 0)   ++
                 show (Label trLbl) 


compileExpAnd :: Env -> Exp -> Exp -> (Code, Env)
compileExpAnd  env exp1 exp2 = (code, (enlargeStack env3 2))
    where (code1, env1) = compileExp env exp1
          (code2, env2) = compileExp env1 exp2
          (end, env3) = newLabel env2
          endLbl = "l" ++ (show end)
          code = show (PushInt 0)    ++
                 show (PushInt 0)    ++
                 code1               ++
                 show (CmpEq endLbl) ++
                 show (PushInt 0)    ++
                 code2               ++
                 show (CmpEq endLbl) ++
                 show (Pop)          ++
                 show (PushInt 1)    ++
                 show (Label endLbl)


compileExpOr :: Env -> Exp -> Exp -> (Code, Env)
compileExpOr   env exp1 exp2 = (code, (enlargeStack env3 2))
    where (code1, env1) = compileExp env exp1
          (code2, env2) = compileExp env1 exp2
          (end, env3) = newLabel env2
          endLbl = "l" ++ (show end)
          code = show (PushInt 1)    ++
                 show (PushInt 1)    ++
                 code1               ++
                 show (CmpEq endLbl) ++
                 show (PushInt 1)    ++
                 code2               ++
                 show (CmpEq endLbl) ++
                 show (Pop)          ++
                 show (PushInt 0)    ++
                 show (Label endLbl)