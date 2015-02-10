{-

A basic interpreter for a purely functional subset of Scheme named SkimScheme.
Part of this interpreter has been derived from the "Write Yourself a Scheme in
48 Hours - An Introduction to Haskell through Example", by Jonathan Tang. It
does not implement a number of Scheme's constructs. Moreover, it uses a
different approach to implement mutable state within the language.

The name "SkimScheme" refers to the stripped down nature of this interpreter.
According to the New Oxford American Dictionary, "skim" can mean:

(as a verb) ... read (something) quickly or cursorily so as to note only
the important points.

(as a noun) ... an act of reading something quickly or superficially. 

"skimmed/skim milk" is milk from which the cream has been removed. 

The name emphasizes that we do not want to cover the entire standard, small as
it may be. Instead, we want to focus on some of the important aspects, taking a
language implementer's point of view, with the goal of using it as a teaching
tool. Many, many, many aspects of Scheme standards are not covered (it does not
even support recursion!).

Written by Fernando Castor
Started at: August 28th 2012
Last update: December 17th 2012

-}

module Main where
import System.Environment
import Control.Monad
import Data.Map as Map
import LispVal
import SSParser
import SSPrettyPrinter

-----------------------------------------------------------
--                      INTERPRETER                      --
-----------------------------------------------------------
eval :: StateT -> LispVal -> StateTransformer LispVal
eval env val@(String _) = return val
eval env val@(Atom var) = stateLookup env var 
eval env val@(Number _) = return val
eval env (List val@([Number _]))= return (val !! 0)
eval env val@(Bool _) = return val
eval env (List [Atom "quote", val]) = return val
eval env ifi@(List [Atom "if", (List predi), (List conseq), (List alt)]) = 
        do result <- eval env (List predi)
           case result of
               error@(Error _) -> return error
               Bool False -> eval env (List alt)
               otherwise -> eval env (List conseq)
eval env (List (Atom "begin":[v])) = eval env v
eval env (List (Atom "begin": l: ls)) = (eval env l) >>= (\v -> case v of { (error@(Error _)) -> return error; otherwise -> eval env (List (Atom "begin": ls))})
eval env (List (Atom "begin":[])) = return (List [])
eval env lam@(List (Atom "lambda":(List formals):body:[])) = return lam

--eval env clo@(List (Atom "make-closure":(Atom "lambda":(List formals):body:[]))) = return (List (Atom "make-closure":(Atom "lambda":(List (formals ++ evalBack env 0 (size env))):body:[])))  

-- fazer lookup "let" em env, buscar var em formals; usar >>=
 
-- evalBack env "let" >>= (\v -> case v of { (error@(Error _)) -> return clo; otherwise -> eval env (List (Atom "lambda":(List formals):body:[]))})


-- The following line is slightly more complex because we are addressing the
-- case where define is redefined by the user (whatever is the user's reason
-- for doing so. The problem is that redefining define does not have
-- the same semantics as redefining other functions, since define is not
-- stored as a regular function because of its return type.

eval env (List [Atom "let", List escope, body]) = 
  ST (\s e -> let
                (ST f) = applyLet env escope body  
                (res, newStateS, newStateE) = f s e              
                listVars = [var | List [var, val] <- escope ]  
                boolNotCopies = (length listVars) == (length (removeCopies listVars))
            in if (boolNotCopies) then (res, newStateS, e)
               else (Error ("let tem copias de variaveis locais"), s, e)
      )

-- Tentativa 2 de fazer funcao make-closure
{-eval env lis@(List [Atom "make-closure2", lambda]) = -- testei com lambda com o padrao (Atom escope, body) e deu erro; ebl4
  ST (\s e -> let
                (ST f) = eval env lambda 
                -- (ST f) = eval env escope body  
                (res, newStateS, newStateE) = f s e              
                -- listVars = [var | List [var, val] <- escope ]  
                -- boolNotCopies = (length listVars) == (length (removeCopies listVars))
            in (res, newStateS, newStateE) -- if (not boolNotCopies) then (res, newStateS, newStateE) -- neste caso, a make-closure devolve o ambiente local modificado de acordo com o que já tinha              
               -- else (Error ("lambda tem copias de parametros"), s, e)
      )
-}
eval env (List (Atom "define": args)) = maybe (define env args) (\v -> return v) (Map.lookup "define" env)
-- lookup :: Ord k => k -> Map k a -> Maybe a
-- maybe :: b -> (a -> b) -> Maybe a -> b
eval env (List (Atom "set!": args)) = applySet env args


-- avaliacao para funcoes recursivas
eval env (List (listF@(List _): args)) = eval env listF >>= (\v -> case v of {(Native f) -> return (f args); otherwise -> return (Error "not a recursive function")})

--eval env (List (Atom "let": args))
eval env (List (Atom func : args)) = mapM (eval env) args >>= apply env func  

-- mapM (eval env) args :: StateTransformer [LispVal]
-- apply env func :: [LispVal] -> StateTransformer LispVal
-- mapM :: Monad m => (a -> m b) -> [a] -> m [b]
-- apply :: StateT -> String -> [LispVal] -> StateTransformer LispVal

eval env (Error s)  = return (Error s)
eval env form = return (Error ("Could not eval the special form: " ++ (show form)))

stateLookup :: StateT -> String -> StateTransformer LispVal
stateLookup env var = ST $ 
  (\s e -> 
    (maybe (Error "variable does not exist.") 
           id (Map.lookup var (union env (union s e)) 
    ), s, e))

--removeCopies :: (Eq a) => [a] -> [a]
removeCopies [] = []
removeCopies (x:xs) = x: removeCopies (Prelude.filter (\y -> (x /= y)) xs)

-- evalBack :: StateT -> Int -> StateTransformer LispVal


--  recebe o ambiente env e um index e retorna uma lista de variaveis do env presentes no ambiente e
{-evalBack env index = ST $ 
  (\s e -> 
    (List (envVar env e index)
    , s, e))-}


-- funcao que retorna variaveis do env presentes no ambiente e
envVar env e index = 
  if (index < size env) then
      case (retornaVars env index) of 
          (Atom var) -> 
              case (Map.lookup var e) of 
                  Just (x) -> [x] ++ envVar env e (index+1) -- encontrou no ambiente e (local)
                  otherwise -> envVar env e (index+1) -- nao encontrou no ambiente (busca o proximo elemento no env)
          otherwise -> envVar env e (index+1) -- nao e uma variavel, busca o proximo elemento no env
  else []

   
retornaVars env index = 
  if (index < size env) then 
        case snd (Map.elemAt index env) of
            Just (Atom var) -> (Atom var)
            otherwise -> retornaVars env (index+1)
  else (Error "sem variavel")

            
 {-   (if (index < size e) then 
        (case snd (Map.elemAt index e) of
            Just (Native elements) -> (evalBack env (index+1))
            otherwise ->  
                case snd (Map.elemAt index env) of
                    Just (Atom var) -> Atom var
                    otherwise -> Atom [])
    else Atom []), s, e)-}
    
{-
-- newEnv :: StateT -> Int -> StateT
newEnv env index = if ("let" == fst (Map.elemAt index env)) then (Map.deleteAt index env)
                   else newEnv (Map.deleteAt index env) (index+1)-}

applySet :: StateT -> [LispVal] -> StateTransformer LispVal
applySet env [(Atom id), val] = 
  ST (\s e -> let 
                (ST f)    = eval env val
                (result, newStateS, newStateE) = f s e
            in 
        if (member id newStateE) then (result, newStateS, (insert id result newStateE))                           
        else if (member id newStateS) then (result, (insert id result newStateS), newStateE)         
        else (Error "variable does not exist.", newStateS, newStateE) 
              
    )

applySet env args = return (Error "wrong number of arguments") 

-- aplica a funcao defineLet para inserir a variavel com seu valor no ambiente em seguida 
-- ligação direta, direct bind >> com a avaliacao do corpo do let

applyLet env bind@(List [Atom id, val]:[]) body = (defineLet env id val) >> eval env body
applyLet env bind@(List [Atom id, val]:xs) body = (defineLet env id val) >> eval env body
applyLet env list _ = ST (\s e -> (Error "not a let", s, e))
                

-- funcao de definicao de variaveis locais. Inserindo a variavel com valor avaliado no ambiente local
defineLet env id val = 
    ST (\s e -> let 
                   (ST f) = eval env val
                   (res, newStateS, newStateE) = f s e
                   in (res, newStateS, (insert id res newStateE))
       )

--applyLet env [(Atom id), val] =                 

-- Because of monad complications, define is a separate function that is not
-- included in the state of the program. This saves  us from having to make
-- every predefined function return a StateTransformer, which would also
-- complicate state management. The same principle applies to set!. We are still
-- not talking about local definitions. That's a completely different
-- beast.
define :: StateT -> [LispVal] -> StateTransformer LispVal
define env [(Atom id), val] = defineVar env id val
define env [(List [Atom id]), val] = defineVar env id val
--define env [(Atom id), (List (Atom "make-closure"):val)] = 
define env args = return (Error "wrong number of arguments")
defineVar env id val = 
  ST (\s e -> let 
                (ST f)    = eval env val
                (result, newState, newStateE) = f s e
            in  (result, (insert id result newState), e)
     )

-- The maybe function yields a value of type b if the evaluation of 
-- its third argument yields Nothing. In case it yields Just x, maybe
-- applies its second argument f to x and yields (f x) as its result.
-- maybe :: b -> (a -> b) -> Maybe a -> b
apply :: StateT -> String -> [LispVal] -> StateTransformer LispVal
apply env func args =  
                  case (Map.lookup func env) of
                      Just (Native f)  -> return (f args)
                      otherwise -> 
                        (stateLookup env func >>= \res -> 
                          case res of 
                            List (Atom "lambda" : List formals : body:l) -> lambda env formals body args                              
                            otherwise -> return (Error "not a function.")
                        )

--applyRec env func args = 
--                  case (Map.lookup func env) of
--                       Just (Native)
 
-- The lambda function is an auxiliary function responsible for
-- applying user-defined functions, instead of native ones. We use a very stupid 
-- kind of dynamic variable (parameter) scoping that does not even support
-- recursion. This has to be fixed in the project.
lambda :: StateT -> [LispVal] -> LispVal -> [LispVal] -> StateTransformer LispVal
lambda env formals body args = 
  let dynEnv = Prelude.foldr (\(Atom f, a) m -> Map.insert f a m) env (zip formals args)
  in  eval dynEnv body
-- foldr :: (a -> b -> b) -> b -> [a] -> b
-- zip :: [a] -> [b] -> [(a, b)]



-- Initial environment of the programs. Maps identifiers to values. 
-- Initially, maps function names to function values, but there's 
-- nothing stopping it from storing general values (e.g., well-known
-- constants, such as pi). The initial environment includes all the 
-- functions that are available for programmers.
environment :: Map String LispVal
environment =   
            insert "number?"        (Native predNumber)
          $ insert "boolean?"       (Native predBoolean)
          $ insert "list?"          (Native predList)
          $ insert "+"              (Native numericSum) 
          $ insert "*"              (Native numericMult) 
          $ insert "-"              (Native numericSub) 
          $ insert "/"              (Native numericDiv)
          $ insert "car"            (Native car)           
          $ insert "cdr"            (Native cdr)   
          $ insert "eq?"            (Native predEq)
          $ insert "fib"            (Native fib)
          $ insert "cons"           (Native cons)
          $ insert "mod"            (Native numericMod)
          $ insert "lt?"            (Native predLt)
            empty

type StateT = Map String LispVal

-- StateTransformer is a data type that embodies computations
-- that transform the state of the interpreter (add new (String, LispVal)
-- pairs to the state variable). The ST constructor receives a function
-- because a StateTransformer gets the previous state of the interpreter 
-- and, based on that state, performs a computation that might yield a modified
-- state (a modification of the previous one). 


-- StateTransformer foi modificado para incluir um novo StateT que representa os campos destinados ás variaveis locais
-- definidas com let
data StateTransformer t = ST (StateT -> StateT -> (t, StateT, StateT))

instance Monad StateTransformer where
  return x = ST (\s e -> (x, s, e))
  (>>=) (ST m) f = ST (\s e -> let 
                                 (v, newS, newE) = m s e
                                 (ST resF) = f v
                             in  resF newS  newE
                      )


instance Eq LispVal where
    (Number a) == (Number b) = (a) == (b)
    (String a) == (String b) = (a) == (b)
    (Atom a) == (Atom b) = (a) == (b)    
    Bool a == Bool b = (a) == (b)
    List a == List b = (a) == (b)  
    DottedList [a1] a2 == DottedList [b1] b2 = (a1 == b1) && (a2 == b2)
    (Error a) == (Error b) = (a) == (b)
    -- observacao, pois (eq? a b) retorna #t. De fato, pois sao dois erros do mesmo tipo
    _ == _ = False    




--  DottedList (a:as) c == DottedList (b:bs) d = (a == b) && (c == d) && (DottedList as c == DottedList bs d)
  --  DottedList [] c == DottedList [] d = (c == d)
  --  DottedList _ c == DottedList _ d = False
  --  List [] == List [] = True   
  -- List (l:ls) == List (a:as) = (l == a) && (List ls == List as)
  --  List _ == List _ = False    
-----------------------------------------------------------
--          HARDWIRED PREDEFINED LISP FUNCTIONS          --
-----------------------------------------------------------

-- Includes some auxiliary functions. Does not include functions that modify
-- state. These functions, such as define and set!, must run within the
-- StateTransformer monad. 

fib :: [LispVal] -> LispVal
fib (Number a : []) = Number (fibo a)
fib ls = Error "wrong number of arguments"

fibo 0 = 1
fibo n = n*(fibo (n-1))

cons :: [LispVal] -> LispVal
cons [a, List []] = List [a]
cons [a, List as] = List $ a:as
cons [a, DottedList b bs] = DottedList (a:b) bs
cons [a, b] = DottedList [a] b

car :: [LispVal] -> LispVal
car [List (a:as)] = a
car [DottedList (a:as) _] = a
car ls = Error "invalid list."

cdr :: [LispVal] -> LispVal
cdr (List (a:as) : ls) = List as
cdr (DottedList (a:[]) c : ls) = c
cdr (DottedList (a:as) c : ls) = DottedList as c
cdr ls = Error "invalid list."

predNumber :: [LispVal] -> LispVal
predNumber (Number _ : []) = Bool True
predNumber (a:[]) = Bool False
predNumber ls = Error "wrong number of arguments."

predBoolean :: [LispVal] -> LispVal
predBoolean (Bool _ : []) = Bool True
predBoolean (a:[]) = Bool False
predBoolean ls = Error "wrong number of arguments."

predList :: [LispVal] -> LispVal
predList (List _ : []) = Bool True
predList (a:[]) = Bool False
predList ls = Error "wrong number of arguments."

-- We are considering that (<) and (mod) are not associative.

predLt :: [LispVal] -> LispVal
predLt (Number n1:Number n2:[]) = Bool (n1 < n2)
predLt _ = Error "wrong number of arguments"

predEq :: [LispVal] -> LispVal
predEq lista@ (Bool _ : as: []) = eqExec lista
predEq lista@ (Number _ : as: []) = eqExec lista
predEq lista@ (String _ : as: []) = eqExec lista
predEq lista@ (List _ : as: []) = eqExec lista
predEq lista@ (Atom _ : as: []) = eqExec lista
predEq lista@ (as: [List _]) = eqExec lista
predEq lista@ (as: [DottedList [list] b]) = eqExec lista
predEq lista@ (a:as) = eqExec lista


eqExec (x:xs) = equal (x:xs)

equal :: [LispVal] -> LispVal
equal [] = Error "wrong number of arguments"
equal [l] = Error "wrong number of arguments"
equal (l:[lw]) = Bool (evalB (==) l lw)
equal l = Error "wrong number of arguments"


-- function that make evaluation if two list are equals
evalB :: (LispVal -> LispVal -> Bool) -> LispVal -> LispVal -> Bool
evalB op l lx = op l lx

containsZero :: [Integer] -> Bool
containsZero [] = False
containsZero (x:xs) | (x == 0) = True
                    | otherwise = containsZero xs

-- Division is left-associative
numericDiv :: [LispVal] -> LispVal
numericDiv [] = Number 1
numericDiv l = numericBinOpDiv div l

numericSum :: [LispVal] -> LispVal
numericSum [] = Number 0
numericSum l = numericBinOp (+) l

numericMult :: [LispVal] -> LispVal
numericMult [] = Number 1
numericMult l = numericBinOp (*) l

numericSub :: [LispVal] -> LispVal
numericSub [] = Error "wrong number of arguments."
-- The following case handles negative number literals.
numericSub [x] = if onlyNumbers [x]
                 then (\num -> (Number (- num))) (unpackNum x)
                 else Error "not a number."
numericSub l = numericBinOp (-) l

numericMod :: [LispVal] -> LispVal
numericMod (Number a:Number b:[]) = if b == 0 then Error "cannot divide by zero."
                                    else (Number (mod a b))

-- We have not implemented division. Also, notice that we have not 
-- addressed floating-point numbers.

numericBinOp :: (Integer -> Integer -> Integer) -> [LispVal] -> LispVal
numericBinOp op args = if onlyNumbers args 
                       then Number $ foldl1 op $ Prelude.map unpackNum args 
                       else Error "not a number."

numericBinOpDiv :: (Integer -> Integer -> Integer) -> [LispVal] -> LispVal
numericBinOpDiv op args = if onlyNumbers args 
                          then let numbers = Prelude.map unpackNum args
                               in if containsZero $ tail numbers then Error "cannot divide by zero."
                                  else Number $ foldl1 op numbers
                          else Error "not a number."
                       
onlyNumbers :: [LispVal] -> Bool
onlyNumbers [] = True
onlyNumbers (Number n:ns) = onlyNumbers ns
onlyNumbers ns = False             
                       
unpackNum :: LispVal -> Integer
unpackNum (Number n) = n
--- unpackNum a = ... -- Should never happen!!!!


-----------------------------------------------------------
--                     main FUNCTION                     --
-----------------------------------------------------------

comandoValido :: LispVal -> Bool
comandoValido (List ((Atom "comment"):xs)) = False
comandoValido _ = True
filtrarComentarios :: LispVal -> LispVal
filtrarComentarios (List l) = (List (Prelude.map filtrarComentarios $ Prelude.filter comandoValido l))
filtrarComentarios lv = lv

showResult :: (LispVal, StateT, StateT) -> String
showResult (val, defs, lets) = show val ++ "\n" ++ show (toList defs) ++ "\n"

getResult :: StateTransformer LispVal -> (LispVal, StateT, StateT)
getResult (ST f) = f environment empty -- we start with an empty state. 

main :: IO ()
main = do args <- getArgs
          putStr $ showResult $ getResult $ eval environment $ filtrarComentarios $ readExpr $ concat $ args
          











--(begin (define f (lambda (x) (+ x 10))) (define result (f (car '(50 34 567 433 22 23 2345 "ok" (6 87 6))))) result)


--(begin (let ((i 0))(define f (lambda (y)(i+y))))(define val1 (f 1))(define val2 (f 1))(+ val1 val2))
