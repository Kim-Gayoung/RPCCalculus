module Ast where

import Data.List 

data Obj = L [Obj] | I Integer | D Double | S String | P String | F [String] Obj Env deriving (Show, Eq)

type Env = [(String,Obj)]

prim_name
     = [ "+", "-", "*", "/"
        , ">", "<", ">=", "<=", "="
        , "abs", "append", "apply", "begin"
        , "car", "cdr", "cons", "eq?", "equal?"
        , "length", "list", "list?", "map", "max", "min"
        , "not", "null?", "number?", "procedure?", "round", "symbol?"
        , "sin", "cos", "tan", "sqrt", "pow" 
        , "pi" 
        , "read", "print"
        ]  -- constant

{-
 AST ::= 
      S sym |  I i | D d
    | L [S "quote", AST]
    | L [S "if", AST, AST, AST]
    | L [S "define", S sym, AST]
    | L [S "set!", S sym, AST]
    | L [S "lambda", L params, AST]
    | L [S "begin", AST1, ..., ASTn]
    | L [AST1, ..., ASTn]
-}

fv :: [String] -> Obj -> [String]
fv bvs (S x) = if x `elem` bvs || x `elem` prim_name then [] else [x]
fv bvs (I i) = []
fv bvs (D d) = []
fv bvs (L [S "quote", e]) = []
fv bvs (L [S "if", cond, et, ee]) = fv bvs cond `union` fv bvs et `union` fv bvs ee
fv bvs (L [S "define", S x, e]) = fv (x:bvs) e
fv bvs (L [S "let", S x, e, e']) = fv (x:bvs) e `union` [ y | y <- fv (x:bvs) e', x /= y]
fv bvs (L [S "set!", S x, e]) = fv bvs e
fv bvs (L [S "lambda", L params, e]) = [ y | y <- fv ([x | S x <- params] ++ bvs) e, not (S y `elem` params)]
fv bvs (L [S "lambda", S cs, L params, e]) = [ y | y <- fv ([x | S x <- params] ++ bvs) e, not (S y `elem` params)]
fv bvs (L [S "lambda", S cs, S name, L params, e]) = [ y | y <- fv ([x | S x <- params] ++ bvs) e, not (S y `elem` params)]
fv bvs (L ((S "begin") : es)) = fv_begin bvs es
fv bvs (L es) = foldr union [] $ map (fv bvs) es
fv bvs _ = [] -- Any better way to handle this?

fv_begin bvs [] = []
fv_begin bvs (e@(L [S "define", S x, def]) : es) = fv (x:bvs) def `union` fv_begin (x:bvs) es
fv_begin bvs (e@(L [S "set!", S x, def]) : es) = fv bvs def `union` fv_begin (x:bvs) es
fv_begin bvs (e:es) = fv bvs e `union` fv_begin bvs es

mkBeginStr sexps = "(begin " ++ concat sexps ++ ")"
mkBegin exps = L $ [S "begin"] ++ exps


pprint :: Int -> Obj -> String
pprint level obj = indent level ++ toStr level obj

toStr level (S x) = x
toStr level (I i) = show i
toStr level (D d) = show d
toStr level (L [S "quote", e]) = op ++ "quote " ++ toStr level e ++ ep
toStr level (L [S "if", cond, ethen, eelse]) = 
  op ++ "if " ++ toStr level cond ++ cr 
  ++ pprint (level+1) ethen ++ cr
  ++ pprint (level+1) eelse ++ ep
toStr level (L [S "define", S x, e]) =
  op ++ "define " ++ x ++ cr ++ pprint (level+1) e ++ cr
toStr level (L [S "let", S x, e, e']) =
  op ++ "let " ++ x ++ cr ++ pprint (level+1) e ++ cr ++ pprint (level+1) e' ++ ep
toStr level (L [S "set!", S x, e]) =
  op ++ "set! " ++ x ++ sp ++ toStr level e ++ ep ++ cr
toStr level (L [S "lambda", L xs, e]) =
  op ++ "lambda " ++ toList [ x | S x <- xs] ++ cr ++ pprint (level+1) e ++ ep
toStr level (L [S "lambda", S cs, L xs, e]) =
  op ++ "lambda " ++ cs ++ sp ++ toList [ x | S x <- xs] ++ cr ++ pprint (level+1) e ++ ep
toStr level (L [S "lambda", S cs, S name, L xs, e]) =
  op ++ "lambda " ++ cs ++ sp ++ name ++ sp ++ toList [ x | S x <- xs] ++ cr ++ pprint (level+1) e ++ ep  
toStr level (L (S "begin" : es)) = 
  op ++ "begin" ++ cr ++
  concat (map (pprint (level+1)) es) ++ ep
toStr level (L es) =
  toList (map (toStr level) es)
toStr level (F xs e _) =
  op ++ "lambda " ++ sp ++ show xs ++ sp ++ toStr level e ++ ep  -- free variable?

toList :: [String] -> String
toList xs = op ++ toList' xs ++ ep

toList' [] = ""
toList' [x] = x
toList' (x:xs) = x ++ sp ++ toList' xs

cr = "\n"
op = "("
ep = ")"
sp = " "

indent :: Int -> String
indent level = concat $ take level $ repeat "  "