--
-- A Haskell Implementation of RPC calculus for Little Scheme 
-- by Kwanghoon Choi
--    cf. Ezra E. K. Cooper and Philip Wadler's PPDP 2009
--

module Compile where

import Ast
import Data.List

-------------------------------------------------
type State = (Int)

data K a = K (State -> (a, State))

instance Functor K where
  fmap f (K g) = K (\i -> 
                    let (a, i') = g i
                    in  (f a, i'))

instance Applicative K where
  pure x = K (\i -> (x,i))
  (K f) <*> (K x) = K (\i -> let (ab, i') = f i 
                                 (a,  i'') = x i'
                             in  (ab a, i''))

instance Monad K where
  return x  = K (\i -> (x, i))
  (>>=) (K g) f = K (\i -> let (r,i') = g i 
                               K h    = f r
                           in  h i')

newLambda = newName "lambda_"
  
newCont = newName "cont_"

newBegin = newName "begin_"

newName :: String -> K String
newName name = 
  K (\state -> 
    let i = state
        state' = i+1
    in  (name ++ show i, state'))    

--------------------------------------------

capply = S "$capply"
cfun = S "$fun"
carg = S "$arg"
tramp = S "$tramp"
cx = S "$x"
call = S "Call"
ret = S "Return"
req = S "req"

sapply = S "$sapply"
cont = S "$cont"
sfun = S "$fun"
sarg = S "$arg"
sk = S "$k"
sx' = S "$x'"
app = S "App"
fin = S "Fin"

cons = S "cons"
car = S "car"
cdr = S "cdr"
quote = S "quote"
equal = S "equal?"
begin = S "begin"
define = S "define"
lambda = S "lambda"
lif = S "if"
set = S "set!"
list = S "list"
llet = S "let"

ifcont = S "$ifcont"
thencont = S "$thencont"
elsecont = S "$elsecont"
letcont = S "letcont"
defcont = S "$defcont"

setcont = S "$set!cont"

--------------------------------------------
-- Server/client compilation
--------------------------------------------
type Alts = [(String, [String], Obj)]

compile :: Obj -> (Obj, Obj)
compile exp = 
  case compileBoth exp of
    K f -> case f 1 of
            (exp_cs, _) -> exp_cs

compileBoth :: Obj -> K (Obj, Obj)
compileBoth exp = do
  explicit_exp <- explicit exp
  exp_c <- compCtop explicit_exp
  exp_s <- compStop explicit_exp
  return (exp_c, exp_s)

-- for both sides
explicit :: Obj -> K Obj
explicit (S x) = return $ S x
explicit (I i) = return $ I i
explicit (D d) = return $ D d
explicit (L [S "quote", exp]) = do
  exp' <- explicit exp
  return $ L [S "quote", exp']
explicit (L [S "if", cond, thenexp, elseexp]) = do
  cond' <- explicit cond
  thenexp' <- explicit thenexp
  elseexp' <- explicit elseexp
  return $ L [S "if", cond', thenexp', elseexp']
explicit (L [S "define", S x, exp]) = do
  exp' <- explicit exp
  return $ L [S "define", S x, exp']
explicit (L [S "set!", S x, exp]) = do
  exp' <- explicit exp
  return $ L [S "set!", S x, exp']
explicit (L [S "lambda", S cs, L xs, exp]) = do
  fun_name <- newLambda
  exp' <- explicit exp
  return $ L [S "lambda", S cs, S fun_name, L xs, exp']
explicit (L (S "begin" : exps)) = do
  exps' <- mapM explicit exps
  return $ L (S "begin" : exps')
explicit (L exps) = do
  exps' <- mapM explicit exps
  return $ L exps'

-- Client side compilation
compCtop :: Obj -> K Obj
compCtop m = do
  (m', alts) <- compCfun m
  return $ buildCtop alts m'

buildCtop :: Alts -> Obj -> Obj
buildCtop alts m = 
  L [
    begin,
    L [ define, capply, L [ lambda, L [cfun, carg], applybody alts] ],
    L [ define, tramp, L [ lambda, L [cx], ctrampbody] ],
    m
  ]

applybody :: Alts -> Obj
applybody [] = L []
applybody ((l,ys,m):alts) =
  L [ lif, L [equal, L[car, cfun], L[quote, S l]]  -- (if (equal? (car (cdr arg)) 'l)
    , mkAlt ys (L [cdr, cfun]) m
    , applybody alts
  ]

ctrampbody = L [
  lif, L [equal, L [car, cx], L [quote, call]],  -- if x = Call (f, x, k)
    let f = "f" in
    let x = "x" in
    let k = "k" in
    mkAlt [f, x, k] (L [cdr, cx])
      (L [tramp, L [ L [quote, req], cont, L [S k, L [ capply, S f, S x] ]]]),
    L [car, L [cdr, cx]]  -- otherwise, x = Return x
  ]

mkAlt :: [String] -> Obj -> Obj -> Obj
mkAlt []     arg e = e
mkAlt (y:ys) arg e = L [llet, (S y), L[car, arg], mkAlt ys (L[cdr, arg]) e]

compCfun :: Obj -> K (Obj, Alts)
compCfun (S x) = return (S x, [])
compCfun (I i) = return (I i, [])
compCfun (D d) = return (D d, [])
compCfun (L [S "quote", exp]) = return (L [S "quote", exp], [])
compCfun (L [S "if", cond, thenexp, elseexp]) = do
  (cond', alts_cond) <- compCfun cond
  (thenexp', alts_then) <- compCfun thenexp
  (elseexp', alts_else) <- compCfun elseexp
  return $ (L [S "if", cond', thenexp', elseexp'], alts_cond `union` alts_then `union` alts_else)
compCfun (L [S "let", S x, exp1, exp2]) = do
  (exp1', alts1) <- compCfun exp1
  (exp2', alts2) <- compCfun exp2
  return $ (L [llet, S x, exp1', exp2'], alts1 `union` alts2)
compCfun (L [S "define", S x, exp]) = do 
  (exp', alts) <- compCfun exp
  return $ (L [S "define", S x, exp'], alts)
compCfun (L [S "set!", S x, exp]) = do
  (exp', alts) <- compCfun exp
  return $ (L [S "set!", S x, exp'], alts)
compCfun (L [S "lambda", S "c", S name, L xs, exp]) = genCCLambda name xs exp
compCfun (L [S "lambda", S "s", S name, L xs, exp]) = genCSLambda name xs exp
compCfun (L (S "begin" : exps)) = do
   (exps', alts) <- compCfunExps exps
   return $ (L (S "begin" : exps'), alts)
compCfun (L []) = return (L [], [])
compCfun (L [exp]) = do
   (exp', alts) <- compCfun exp
   return $ (L [exp'], alts)
compCfun (L exps) = do
   (exp, alts) <- genApply exps
   return $ (exp, alts)

compCfunExps :: [Obj] -> K ([Obj], Alts)
compCfunExps [] = return ([], [])
compCfunExps (e:es) = do
  (e', alts1) <- compCfun e
  (es', alts2) <- compCfunExps es
  return (e':es', alts1 `union` alts2)

genApply (exp:es) = do 
  (exp1, alts1) <- compCfun exp
  genApply' (\exp2 alts2 -> return $ (L [capply, exp1, exp2], alts1 ++ alts2)) es

genApply' f [exp] = do
  (exp', alts') <- compCfun exp
  f exp' alts'
genApply' f (exp:exps) = do 
  (exp_, alts_) <- compCfun exp
  (exp', alts') <- f exp_ alts_
  let f' exp2 alts2 = return $ (L [capply, exp', exp2], alts'++alts2 )
  genApply' f' exps

mkClosure :: String -> [String] -> Obj
mkClosure f fvs = L [list, L (L [ quote, S f] : mkList fvs)]
  where
    mkList [] = []
    mkList (fv:fvs) = S fv : mkList fvs

genCCLambda :: String -> [Obj] -> Obj -> K (Obj, Alts)
genCCLambda name [x] exp = do
  (exp', alts) <- compCfun exp
  let fun_name = name ++ "_1"
  let S xname = x
  let fvs = fv [] (L [lambda, L [x], exp])
  let alt = (fun_name, fvs, L [llet, S xname, carg, exp'])
  return (mkClosure fun_name fvs, alt:alts)
genCCLambda name (x:xs) exp = do
  (exp', alts) <- genCCLambda name xs exp 
  let fun_name = name ++ show (length (x:xs))
  let fvs = fv [] (L [lambda, L (x:xs), exp])
  let S xname = x
  let alt = (fun_name, fvs, L [llet, S xname, carg, exp'])
  return (mkClosure fun_name fvs, alt:alts)

genCSLambda :: String -> [Obj] -> Obj -> K (Obj, Alts)
genCSLambda name [x] exp = do
  (exp', alts) <- compCfun exp
  let fun_name = name ++ "_1"
  let fvs = fv [] (L [S "lambda", L [x], exp])
  let tramp_reqapply = 
        L [llet, S "f", mkClosure fun_name fvs, 
          L [ llet, S "k", L [list, L[ L [quote, fin] ]],
            L [ tramp, L [ list, L [L [quote, req], sapply, L [S "f", carg, S "k"]] ]  ] ] ]
  let alt = (fun_name, fvs, tramp_reqapply)
  return (mkClosure fun_name fvs, alt:alts) -- ???

-- compilation for server-side

compStop :: Obj -> K Obj
compStop m = do
  (m', alts1, alts2) <- compSfun m
  return $ buildStop alts1 alts2 

buildStop :: Alts -> Alts -> Obj
buildStop altsfun altscont = 
  L [
    begin,
    L [ define, sapply, L [lambda, L [sfun, sarg, sk], applybody altsfun]],
    L [ define, cont, L [lambda, L [sk, sarg], contbody altscont contbody_end] ]
  ]

contbody :: Alts -> Obj -> Obj
contbody [] exp = exp
contbody ((l,ys,lexp):alts) exp = 
  L [ 
    lif, L [equal, L [car, sk], L[quote, S l]],
    mkAlt ys (L [cdr, sk]) lexp,
    contbody alts exp
  ]

contbody_end =
  L [
    lif, L [equal, L [car, sk], L[quote, app]],
    let S k = sk in
    let S fun = sfun in
      mkAlt [fun, k] (L [cdr, sk])
        (L [sapply, sfun, sarg, sk]),  -- App(fun,k) => apply(fun,arg,k)
    L [list, L[L [quote, ret], sarg]] -- Fin() => Return(arg)
  ]

{-
compSfun: 식 Obj를 받아서 
 - 컴파일식 Obj
 - `eval'하고 컨티뉴에이션에 전달하는 코드에 대한 Alts와
 - `eval'후 대기할 컨티뉴에이션 코드에 대한 Alts로 컴파일
-}
compSfun :: Obj -> K (Obj, Alts, Alts)
compSfun (S x) = return (mkCont sk (S x), [], [])
compSfun (I i) = return (mkCont sk (I i), [], [])
compSfun (D d) = return (mkCont sk (D d), [], [])
compSfun (L [S "quote", exp]) = return (mkCont sk (L [S "quote", exp]), [], [])
{-
  (if cond thenexp elseexp)
  =>
  (let ($k ($ifcont $k)) cond')

  ($ifcont $k) -> 
       (if $arg ($cont $thencont $k) ($cont $elsecont $k))
-}
compSfun (L [S "if", cond, thenexp, elseexp]) = do
  (cond', alts_cond, alts_condk) <- compSfun cond
  (thenexp', alts_then, alts_thenk) <- compSfun thenexp
  (elseexp', alts_else, alts_elsek) <- compSfun elseexp
  ifcontname <- newCont
  let ifcont = S ifcontname
  let S kname = sk  
  let condk = L[list, L [L [quote, ifcont], sk]]
  let condk_fvs_k = (fv [] thenexp `union` fv [] elseexp) ++ [kname]  
  let cond_alt =
       [(ifcontname, condk_fvs_k, 
              (L [lif, sarg, thenexp', elseexp']) )]
  return $ (L [llet, sk, condk, cond'],
    alts_cond `union` alts_then `union` alts_else,
    cond_alt `union` alts_condk `union` alts_thenk `union` alts_elsek)
{-
 (let x exp1 exp2)
 =>
 (let $k ($letcont x fvs_exp2 $k) exp1')
 
 ($letcont x fvs_exp2 $k) -> let x arg exp2'
-}
compSfun (L [S "let", S x, exp1, exp2]) = do
  (exp1', alts1, altscont1) <- compSfun exp1
  (exp2', alts2, altscont2) <- compSfun exp2
  letcontname <- newCont
  let letcont = S letcontname
  let fvs_exp2 = [ y | y <- fv [] exp2, x /= y]
  let S sk_name = sk
  let fv_names_cont = fvs_exp2 ++ [sk_name]
  let letk = L[list, L ([ L [quote, letcont]] ++ [S v | v <- fv_names_cont])]
  let let_alt = (letcontname, fv_names_cont, (L [llet, S x, sarg, exp2']) )
  return $ (L [llet, sk, letk, exp1'],
                  alts1 `union` alts2, [let_alt] `union` altscont1 `union` altscont2)
{-
 (define x exp)
 =>
 (begin
  (define $k' ($defcont x $k))
  (define $k  $k')
  exp')

 ($defcont x $k) -> (begin
                       (define x $arg) 
                       ($cont $k L()))
-}
compSfun (L [S "define", S x, exp]) = do
  (exp', alts, altscont) <- compSfun exp
  defcontname <- newCont
  let defcont = S defcontname
  let defk = L[list, L [ L [quote, defcont], sk]]
  let S sndarg = sk   -- k
  let def_alt = 
       [(defcontname, [],
          mkAlt [sndarg] (L [cdr, sk]) -- TODO: ???
              ( L [ begin 
                  , L [define, S x, sarg]
                  , mkCont sk (L [])]  )) ]
  return $ (L [llet, sk, defk, exp'], 
              alts, def_alt `union` altscont) 
{-
 (set! x exp)
 =>
 (begin
  (define $k' ($set!cont x $k))
  (define $k  $k')
  exp')

 ($set! x $k) -> (begin
                       (set! x $arg) 
                       ($cont $k ()))
-}
compSfun (L [S "set!", S x, exp]) = do
  (exp', alts, altscont) <- compSfun exp
  setcontname <- newCont
  let setcont = S setcontname
  let setk = L[list, L [L [quote, setcont], sk]]
  let S kname = sk  -- k
  let set_alt =
       [(setcontname, [],
          mkAlt [kname] (L [cdr, sk])  -- TODO: ???
              (L [ begin
                 , L [set, S x, sarg]
                 , mkCont sk (L []) ]))]
  return $ (L [llet, sk, setk, exp'],
              alts, set_alt `union` altscont)
compSfun (L [S "lambda", S "c", S name, L xs, exp]) = genSCLambda name xs exp
compSfun (L [S "lambda", S "s", S name, L xs, exp]) = genSSLambda name xs exp
{-
 (begin 
   exp1
   ...
   expn
 )
=>
 [Basic Idea]
 exp1 (\_ ->
  exp2 (\_ ->
   ...
    expn (\x -> k x))

 (begin
   (define k' begincont_2 fvs_e2_en)
   (define k k')
   exp1')


 (begincont_2) -> 
   (begin
     (define k' begincont_3 fvs_e3_en)
     (define k  k')
     exp2')

 ...

 (begincont_n-1) -> 
   (begin
     (define k' begincont_n fvs_en)
     (define k  k')
     expn-1')

 (begincont_n) ->
   expn'
    
-}
compSfun (L (S "begin":[])) = do
  return $ (mkCont sk (L []), [], [])
compSfun (L (S "begin":exps)) = do
  (exp', alts, altscont) <- compSfunBegin exps
  return $ (exp', alts, altscont)
{-
  e1 e2 ... en
  =>
  [Basic Idea]
  en (\xn ->
  en-1 (\xn-1 ->
  ...
  e1 (\f ->
  f ))
-}
compSfun (L []) = return (L [], [], [])
compSfun (L exps) = do
  (exp, alts, altscont) <- genContApply (exps)
  return (exp, alts, altscont)


compSfunBegin [e] = do
  (e', alts1, altscont1) <- compSfun e
  return (e', alts1, altscont1)
compSfunBegin (e:es) = do
  (e', alts1, altscont1) <- compSfun e
  (es', alts2, altscont2) <- compSfunBegin es
  begincontname <- newCont
  let S kname = sk
  let fv_es_k = foldr union [] (map (fv []) es) ++ [kname]
  let e_cont = L[list, L ([ quote, S begincontname ] ++ [S v | v <- fv_es_k]) ]
  let altcont = (begincontname, fv_es_k, es')
  return (L [llet, sk, e_cont, e'], alts1 `union` alts2, 
          [altcont] `union` altscont1 `union` altscont2)

genContApply :: [Obj] -> K (Obj, Alts, Alts)
genContApply [e] = do
  (e', alts, altscont) <- compSfun e
  return (e', alts, altscont)
genContApply (e:es) = do
  (e', alts1, altscont1) <- compSfun e
  (es', alts2, altscont2) <- genContApply es
  contname <- newCont
  let S kname = sk
  let fv_es_k = foldr union [] (map (fv []) es) ++ [kname]
  let e_cont = L [list,  L ([ quote, S contname] ++ [S v | v <- fv_es_k]) ]
  let altcont = (contname, fv_es_k, L [llet, sk, L[list, L[L[quote, app], sarg, sk]], es'])
  return (L [llet, sk, e_cont, e'], alts1 `union` alts2,
          [altcont] `union` altscont1 `union` altscont2)

genSCLambda :: String -> [Obj] -> Obj -> K (Obj, Alts, Alts)
genSCLambda name xs exp = do
  let fvs = fv [] (L [lambda, L xs, exp])
  let fname = name ++ "_1"
  let alt = (fname, fvs, L [list, L ( [L [quote, call], S fname] ++ [S y | y <- fvs] ++ [ sarg, sk ] )] )
  return $ (L [list, L ([L [quote, call]] ++ [S y | y <- fvs]), sarg, sk]
            , [alt], [])
-- genSCLambda name [x] exp = do
--   (exp', alts, altscont) <- compSfun exp
--   let fun_name = name ++ "_1"
--   let fvs = fv [] (L [lambda, L [x], exp])
--   let alt = (fun_name, fvs, exp')
--   return (L [ list, L [L [quote, call], mkClosure fun_name fvs, sarg, sk]]
--           , alt:alts, altscont)
-- genSCLambda name (x:xs) exp = do
--   (exp', alts, altscont) <- genSCLambda name xs exp
--   let fun_name = name ++ show (length (x:xs))
--   let fvs = fv [] (L [lambda, L (x:xs), exp])
--   let alt = (fun_name, fvs, L [llet, x, sarg, exp'])
--   return (mkCont sk (mkClosure fun_name fvs), alt:alts, altscont)

genSSLambda :: String -> [Obj] -> Obj -> K (Obj, Alts, Alts)
genSSLambda name [x] exp = do
  (exp', alts, altscont) <- compSfun exp
  let fun_name = name ++ "_1"
  let fvs = fv [] (L [lambda, L[x], exp])
  let alt = (fun_name, fvs, exp')
  return (mkCont sk (mkClosure fun_name fvs), alt:alts, altscont) -- alt:alts or alts??
genSSLambda name (x:xs) exp = do
  (exp', alts, altscont) <- compSfun exp
  let fun_name = name ++ (show (length (x:xs)))
  let fvs = fv [] (L [lambda, L (x:xs), exp])
  let alt = (fun_name, fvs, exp')
  return (mkCont sk (mkClosure fun_name fvs), alt:alts, altscont)


mkRet :: Obj -> Obj
mkRet x = L [L [quote, ret], x]

mkCont :: Obj -> Obj -> Obj
mkCont k arg = L[ cont, k, arg]

--------------------------------------------

auth_cs = "(let getCredentials \
 \   (lambda c (prompt) \
  \     (let y (print prompt) (read()) ) ) \
\  (let authenticate \
 \   (lambda s (x) \
   \   (let creds (getCredentials (quote (Enter name, password:))) \
    \    (if (equal? creds (quote ezra:opensesame)) \
     \       (quote (the secret document)) \
      \      (quote (Access denied))  ))) \
\  (authenticate ()))"


-- auth_cs = "(begin \
-- \  (define getCredentials \
--  \   (lambda c (prompt) \
--   \     (let y (print prompt) (read()) ) )) \
-- \  (define authenticate \
--  \   (lambda s (x) \
--    \   (let creds (getCredentials (quote (Enter name, password:))) \
--     \    (if (equal? creds (quote ezra:opensesame)) \
--      \       (quote (the secret document)) \
--       \      (quote (Access denied))  )))) \
-- \  (authenticate ()))"