--
-- A Haskell Implementation of Lisp-like Language 
-- by Kwanghoon Choi
--    cf. Peter Novig's Python Implementation : http://norvig.com/lispy.html
--

module Main where

import Data.Maybe
import Text.Read
import Ast
import Compile

main = putStrLn "main"

tokenize :: String -> [String]
tokenize str = words $ concat $ map (\ch -> if ch=='(' || ch==')' then " " ++ [ch] ++ " " else [ch]) str

parse :: String -> Obj
parse program = fst $ read_from_tokens $ tokenize $ program

read_from_tokens :: [String] -> (Obj, [String])
read_from_tokens [] = error "Syntax error: unexpected EOF while reading"
read_from_tokens ("(":tokens) = 
    let build list [] = (list, [])
        build list (token:tokens) =
            if token /= ")"
            then let (list',tokens') = read_from_tokens (token:tokens)
                 in  build (list ++ [list']) tokens'
            else (list, tokens)
        (list'', tokens'') = build [] tokens
    in (L list'', tokens'')
read_from_tokens (")":tokens) = error "Syntax error: unexpected )"
read_from_tokens (token:tokens) = (atom token, tokens)

atom :: String -> Obj
atom token = 
    if isJust (readMaybe token :: Maybe Integer) then I (read token)
    else if isJust (readMaybe token :: Maybe Double) then D (read token)
    else S token



global_env = 
    map (\op -> (op, P op)) 
        [ "+", "-", "*", "/"
        , ">", "<", ">=", "<=", "="
        , "abs", "append", "apply", "begin"
        , "car", "cdr", "cons", "eq?", "equal?"
        , "length", "list", "list?", "map", "max", "min"
        , "not", "null?", "number?", "procedure?", "round", "symbol?"
        , "sin", "cos", "tan", "sqrt", "pow" 
        , "read", "print"
        ] ++
    [ ("pi", D pi) ]

eval :: Obj -> Env -> (Obj, Env)
eval (S sym) env = 
    case lookup sym env of
        Nothing -> error $ "Symbol not defined: " ++ show sym
        Just obj -> (obj, env)
eval (I i) env = (I i, env)
eval (D d) env = (D d, env)
eval (L [S "quote", exp]) env = (exp, env)
eval (L [S "if", test, conseq, alt]) env =
    case eval test env of
        (S "#t", env') -> eval conseq env'
        (S "#f", env') -> eval alt env'
        (L [], env') -> eval alt env'
        (L _, env') -> eval conseq env'
        (obj, env') -> (error $ "Not boolean in if: " ++ show obj)
eval (L (S "if" : therest)) env = error $ "Syntax error in if" ++ show therest
eval (L [S "let", S sym, exp, exp']) env =
    let (obj,env') = eval exp env
        (obj'',env'') = eval exp' ((sym,obj):env')
    in  (obj'', env)
eval (L [S "define", S sym, exp]) env =
    let (obj,env') = eval exp env
        obj' = case obj of { F xs body env -> F xs body ((sym,obj'):env) ; _ -> obj }
    in  (L [], (sym,obj'):env') -- return the empty list ???
eval (L [S "set!", S var, exp]) env = 
    let (val, env') = eval exp env in (L [], update var val env)
eval (L [S "lambda", S sc, L params, body]) env =
    eval (L [S "lambda", L params, body]) env
eval (L [S "lambda", L params, body]) env =
    let f (S x) = x
        f obj   = error $ "Invalid args in lambda: " ++ show obj
    in  (F (map f params) body env, env)
eval (L (S "begin" : args)) env = evalSeq args env -- begin should be here!!
eval (L (f : args)) env =
    let (fobj, env') = eval f env
        (argobjs, env'') = 
            foldl (\(vals,env) arg -> 
                let (vala,enva) = eval arg env in 
                    (vals ++ [vala], enva)) ([], env) args
    in  proc fobj argobjs env''
eval (L []) env = (L [], env) -- return void
eval obj env = error $ show obj

evalSeq [] env = (L [], env) -- return void
evalSeq [e] env = eval e env
evalSeq (e:es) env = 
    let (_, env') = eval e env in
        evalSeq es env'

evalMap :: Obj -> Obj-> Env -> (Obj, Env)
evalMap f (L []) env = (L [], env)
evalMap f (L (h:t)) env =
    let (hobj, env') = proc f [h] env 
        (L tobj, env'') = evalMap f (L t) env'
    in (L (hobj:tobj), env'')
evalMap f objs env = error $ "Invalid list in evalMap" ++ show objs

update x v [] = [(x,v)]
update x v ((y,w):therest) =
    if x==y then ((x,v):therest) else (y,w):update x v therest

proc :: Obj -> [Obj] -> Env -> (Obj, Env)
proc (P prim) args env = procprim prim args env
proc (F xs body closenv) args env =
    if length xs == length args
    then (fst $ eval body (zip xs args ++ closenv), env)   --- Is it correct?
    else if length xs <= length args
    then let (f,env') = eval body (zip xs args ++ closenv) 
             args' = drop (length xs) args
         in  (fst $ eval (L [P "apply", f, L args']) env', env)
    else (F (drop (length args) xs) body (zip xs args ++ closenv), env)
proc f args env = error $ "Not funcion: " ++ show f ++ show args

procprim "pi" [] env = (D pi, env)
procprim "sin" [arg1] env = (atom $ show $ sin (getnumber arg1), env)
procprim "cos" [arg1] env = (atom $ show $ cos (getnumber arg1), env)
procprim "tan" [arg1] env = (atom $ show $ tan (getnumber arg1), env)
procprim "sqrt" [arg1] env = (atom $ show $ sqrt (getnumber arg1), env)
procprim "pow" [arg1,arg2] env = (atom $ show $ (getnumber arg1 ** getnumber arg2), env)
procprim "+" [arg1, arg2] env = (atom $ tru $ (getnumber arg1 + getnumber arg2), env)
procprim "-" [arg1, arg2] env = (atom $ tru $ (getnumber arg1 - getnumber arg2), env)
procprim "*" [arg1, arg2] env = (atom $ tru $ (getnumber arg1 * getnumber arg2), env)
procprim "/" [arg1, arg2] env = (atom $ tru $ (getnumber arg1 / getnumber arg2), env)
procprim ">" [arg1, arg2] env = (if getnumber arg1 > getnumber arg2 then S "#t" else S "#f", env)
procprim "<" [arg1, arg2] env = (if getnumber arg1 < getnumber arg2 then S "#t" else S "#f", env)
procprim ">=" [arg1, arg2] env = (if getnumber arg1 >= getnumber arg2 then S "#t" else S "#f", env)
procprim "<=" [arg1, arg2] env = (if getnumber arg1 <= getnumber arg2 then S "#t" else S "#f", env)
procprim "=" [arg1, arg2] env = (if getnumber arg1 == getnumber arg2 then S "#t" else S "#f", env)
procprim "abs" [arg1] env = (atom $ show $ abs (getnumber arg1), env)
procprim "append" [L l1, L l2] env = (L (l1 ++ l2), env)
procprim "apply" [f, L args] env = proc f args env
procprim "begin" args env = error "begin should not be called here" -- 
procprim "car" [L (arg:_)] env = (arg, env)
procprim "cdr" [L (_:args)] env = (L args, env)
procprim "cons" [ arg1, L arg2 ] env = (L (arg1 : arg2), env)
procprim "eq?" [arg1, arg2] env = (if arg1 == arg2 then S "#t" else S "#f", env)-- Haskell Eq
procprim "equal?" [arg1, arg2] env = (if arg1 == arg2 then S "#t" else S "#f", env) -- Haskell Eq
procprim "length" [L args] env = (I $ fromIntegral $ length $ args, env)
procprim "list" args env = (L args, env)
procprim "list?" [arg] env = (case arg of L _ -> S "#t" ; _ -> S "#f", env)
procprim "map" [f, arg] env = evalMap f arg env
procprim "max" [arg1,arg2] env = (if getnumber arg1 > getnumber arg2 then arg1 else arg2, env)
procprim "min" [arg1,arg2] env = (if getnumber arg1 > getnumber arg2 then arg2 else arg1, env)
procprim "not" [arg] env = (case arg of S "#t" -> S "#f" ; S "#f" -> S "#t", env)
procprim "null?" [arg] env = (case arg of L [] -> S "#t" ; _ -> S "#f", env)
procprim "number?" [arg] env = (case arg of I _ -> S "#t" ; D _ -> S "#t" ; _ -> S "#f", env)
procprim "procedure?" [arg] env = (case arg of P _ -> S "#t" ; F _ _ _ -> S "#t" ; _ -> S "#f", env)
procprim "round" [arg1] env = (atom $ show $ round $ getnumber $ arg1, env)
procprim "symbol?" [arg] env = (case arg of S _ -> S "#t" ; _ -> S "#f", env)
procprim "read" [arg] env = (S "ezra:opensesame", env)
procprim "print" [arg] env = (L [], env)
procprim p args env = error $ show "Prim: " ++ show p ++ " " ++ show args

tru :: Double -> String
tru d = if (fromIntegral (truncate d ) :: Double) == d 
        then show (truncate d)
        else show d

getnumber :: Obj -> Double
getnumber (I i) = read $ show $ i
getnumber (D d) = d
getnumber obj = error $ "Not number: " ++ show obj

repl env = do
    putStr "lisp> "
    line <- getLine
    let (obj,env') = eval (parse line) env
    putStrLn $ toStr 0 $ obj
    repl env'    

run = repl global_env

{-- RPC compilation --}
rpc_compile pgm = do
  let exp = parse pgm
  let (exp_c, exp_s) = compile exp
  let output = "Program:\n"
                ++ pprint 0 exp
                ++ "\n"
                ++ "Client:\n"
                ++ pprint 0 exp_c
                ++ "\n\n"
                ++ "Server:\n"
                ++ pprint 0 exp_s
  writeFile "./output.txt" output

{-- Regression test --}

one_test tc =
    let exps = init tc
        res  = last tc
        l    = show (fst (eval (parse (mkBeginStr exps)) global_env))
        r    = show (parse res)
    in do putStrLn l
          putStrLn r
          putStrLn (show (l == r))

regression_test =  mapM_ one_test parser_test2_input   
regression_test_fv = map (fv [] . parse . mkBeginStr . init) parser_test2_input
regression_test_pprint = mapM_ (\s -> do { putStrLn s; putStrLn "" }) $ map (pprint 0 . parse . mkBeginStr . init) parser_test2_input  

{- Test cases for parser -}
parser_test1 = tokenize parser_test1_input == parser_test1_result

parser_test1_input = "(begin (define r 10) (* pi (* r r)))"
parser_test1_result = ["(", "begin", "(", "define", "r", "10", ")", "(", "*", "pi", "(", "*", "r", "r", ")", ")", ")"]    

parser_test2 = mapM_ (mapM (putStrLn . show . parse)) parser_test2_input

parser_test2_input = [
        circle_area, 
        fact_10,
        fact_100,
        circle_area_fact,
        count_1,
        count_2,
        twice_1,
        repeat_1,
        repeat_2,
        repeat_3,
        repeat_4,
        pow_1,
        range_1,
        fib_range_1,
        fib_range_2
    ]

{- Test cases for Lispy v1 -}
circle_area_fun = "(define circle-area (lambda (r) (* pi (* r r))))"
circle_area = [ 
    circle_area_fun,
    "(circle-area 3)",
    "28.274333877"
    ]

fact_fun = "(define fact (lambda (n) (if (<= n 1) 1 (* n (fact (- n 1))))))"

fact_10 = [
    fact_fun,
    "(fact 10)",
    "3628800"
    ]

fact_100 = [
    fact_fun,
    "(fact 100)",
    "93326215443944152681699238856266700490715968264381621468592963895217599993229915608941463976156518286253697920827223758251185210916864000000000000000000000000"
    ]

circle_area_fact = [
    circle_area_fun,
    fact_fun,
    "(circle-area (fact 10))",
    "4.1369087198e+13"
    ]

define_first = "(define first car)"

define_rest = "(define rest cdr)"

-- count_fun = "(define count (lambda (item L) (if L (+ (equal? item (first L)) (count item (rest L))) 0)))"
count_fun = "(define count (lambda (item L) (if (null? L) 0 (+ (if (equal? item (first L)) 1 0) (count item (rest L))))))"

count_1 = [
    define_first,
    define_rest,
    count_fun,
    "(count 0 (list 0 1 2 3 0 0))",
    "3"
    ]

count_2 = [
    define_first,
    define_rest,
    count_fun,
    "(count (quote the) (quote (the more the merrier the bigger the better)))",
    "4"
    ]

twice_fun = "(define twice (lambda (x) (* 2 x)))"
twice_1 = [
    twice_fun,
    "(twice 5)",
    "10"
    ]

repeat_fun = "(define repeat (lambda (f) (lambda (x) (f (f x)))))"

repeat_1 = [
    twice_fun,
    repeat_fun,
    "((repeat twice) 10)",
    "40"
    ]

repeat_2 = [
    twice_fun,
    repeat_fun,
    "((repeat (repeat twice)) 10)",
    "160"
    ]

repeat_3 = [ 
    twice_fun,
    repeat_fun,
    "((repeat (repeat (repeat twice))) 10)",
    "2560"
    ]

repeat_4 = [
    twice_fun,
    repeat_fun,
    "((repeat (repeat (repeat (repeat twice)))) 10)",
    "655360"
    ]

pow_1 = [
    "(pow 2 16)",
    "65536.0"
    ]

fib_fun = "(define fib (lambda (n) (if (< n 2) 1 (+ (fib (- n 1)) (fib (- n 2))))))"

range_fun = "(define range (lambda (a b) (if (= a b) (quote ()) (cons a (range (+ a 1) b)))))"

range_1 = [
    range_fun,
    "(range 0 10)",
    "(0 1 2 3 4 5 6 7 8 9)"
    ]

fib_range_1 = [
    fib_fun,
    range_fun,
    "(map fib (range 0 10))",
    "(1 1 2 3 5 8 13 21 34 55)"
    ]

fib_range_2 = [
    fib_fun,
    range_fun,
    "(map fib (range 0 20))",
    "(1 1 2 3 5 8 13 21 34 55 89 144 233 377 610 987 1597 2584 4181 6765)"
    ]


auth = "(begin \
\  (define getCredentials \
 \   (lambda (prompt) \
  \     (let y (print prompt) (read()) ) )) \
\  (define authenticate \
 \   (lambda (x) \
   \   (let creds (getCredentials (quote (Enter name, password:))) \
    \    (if (equal? creds (quote ezra:opensesame)) \
     \       (quote (the secret document)) \
      \      (quote (Access denied))  )))) \
\  (authenticate ()))"