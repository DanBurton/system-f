{-# LANGUAGE
    GADTs
  , KindSignatures
  , FlexibleInstances
  #-}

module SystemF (
  -- * Error handling
    ErrOr
  , good
  , err
  , isGood
  , get
  
  -- * Syntax types
  , Type (NumTy, FunTy, VTy)
  , Term
  , V
  
  -- * Primitives
  , num
  , succ
  , v
  , l
  , app
  , tapp
  
  -- * Library
  , id'
  , succ'
  ) where

import Prelude hiding (succ)
import Control.Applicative
import Control.Monad

import Test.QuickCheck

------------------------ prelimiary ---------------------------------

type ErrOr a = Either String a

good :: a -> ErrOr a
good = Right

err :: String-> ErrOr a
err = Left

isGood :: ErrOr a -> Bool
isGood Right{} = True
isGood Left{}  = False

get :: ErrOr a -> a
get (Right x) = x
get (Left e)  = error e

-------------------- data types -------------------------------------

data Primitive :: * -> * where
  Num :: Integer -> Primitive Integer
  Succ :: Primitive (Integer -> Integer)

---------------------------------------------------------------------

data Type :: * -> * where
  NumTy :: Type Integer
  FunTy :: Type a -> Type b -> Type (a -> b)
  VTy :: (Type a -> Type b) -> Type (V a b)
  TyVar :: Char -> Type a

instance Eq (Type a) where
  NumTy == NumTy = True
  (FunTy dom rng) == (FunTy dom' rng') = dom == dom' && rng == rng'
  VTy{} == VTy{} = error "Equality is undefined on forall'd types" -- TODO
  _ == _ = False

instance Show (Type a) where
  show = showTy ("XYZ" ++ ['A' .. 'W'])

showTy :: [Char] -> (Type a) -> String
showTy _ NumTy = "Num"
showTy cs (FunTy dom rng) = "(" ++ showTy cs dom ++ " -> " ++ showTy cs rng ++ ")"
showTy (c:cs) (VTy f) = "(Forall " ++ [c] ++ ". " ++ showTy cs (f (TyVar c)) ++ ")"
showTy [] VTy{} = error "Too many nested type applications"
showTy _ (TyVar t) = [t]

---------------------------------------------------------------------

newtype V a b = V (Type a -> Term b)

---------------------------------------------------------------------

data Term :: * -> * where
  Prim :: Primitive a -> Term a
  Abs :: Type a -> (Term a -> Term b) -> Term (a -> b)
  App :: Term (a -> b) -> Term a -> Term b
  TAbs :: (Type a -> Term b) -> Term (V a b)
  TApp :: Term (V a b) -> Type a -> Term b
  Unknown :: Char -> Term a

instance Show a => Show (Term a) where
  show t = let v = get $ eval t
               ty = get $ typeOf t
           in show v ++ " : " ++ show ty

instance Eq (Term Integer) where
  (==) = undefined

instance Num (Term Integer) where
  fromInteger = num
  (+) = undefined
  (-) = undefined
  (*) = undefined
  abs = undefined
  signum = undefined
  negate = undefined

-------------------------- evaluation -------------------------------

eval' :: Term a -> ErrOr (Term a)
eval' (Prim p)   = good $ Prim p
eval' (Abs t f)  = good $ Abs t f
eval' (TAbs f)   = good $ TAbs f
eval' (App f x)  = do
  f' <- eval' f
  res <- runApp f' <*> eval' x
  eval' res
eval' (TApp f x) = do
  f' <- eval' f
  res <- runTApp f' <*> pure x
  eval' res

eval :: Term a -> ErrOr a
eval t = eval' t >>= valueOf

---------------------------------------------------------------------

valueOf :: Term a -> ErrOr a
valueOf (Prim n) = fromPrim n
valueOf _ = err "Not a value"

fromPrim :: Primitive a -> ErrOr a
fromPrim (Num n) = good n
fromPrim _ = err "fromPrim failed unexpectedly"

---------------------------------------------------------------------

runApp :: Term (a -> b) -> ErrOr (Term a -> Term b)
runApp (Abs t f) = good f
runApp (Prim p) = runAppPrim p
runApp _ = err "unexpected non-abstraction used in application"

runAppPrim :: Primitive (a -> b) -> ErrOr (Term a -> Term b)
runAppPrim Succ = good $ \(Prim (Num n)) -> num (n + 1)

---------------------------------------------------------------------

runTApp :: Term (V a b) -> ErrOr (Type a -> Term b)
runTApp (TAbs f) = good f
runTApp _ = err "runTApp failed unexpectedly"

------------------------ typing -------------------------------------

typeOf :: Term a -> ErrOr (Type a)
typeOf (Prim p)  = good $ primType p
typeOf (Abs t f) = FunTy t <$> typeOf (f (genTy t))
typeOf (TAbs f)  = good $ VTy (\x -> get $ typeOf (f x)) -- potential error
typeOf (App f x) = do
  FunTy dom rng <- typeOf f
  t             <- typeOf x
  if (t == dom)
    then good rng
    else err "function domain does not match application input"
typeOf (TApp f x) = do
  VTy f' <- typeOf f
  good (f' x)
typeOf (Unknown c) = good $ TyVar c

primType :: Primitive a -> Type a
primType Num{} = NumTy
primType Succ  = FunTy NumTy NumTy

genTy :: Type a -> Term a
genTy NumTy = num 0
genTy (FunTy dom rng) = l dom (\_ -> genTy rng)
genTy (VTy f) = TAbs (\x -> genTy (f x))
genTy (TyVar c) = Unknown c

----------------- language primitives -------------------------------

num = Prim . Num
succ = Prim Succ

v = TAbs
l = Abs

app = App
tapp = TApp

-------------------- basic library functions-------------------------

id' = v (\t -> l t (\x -> x))
const' = v (\t1 -> v (\t2 -> l t1 (\x -> l t2 (\_ -> x))))
succ' = l NumTy (\x -> app succ x)

------------------quick checks---------------------------------------

hasValue :: Term a -> Bool
hasValue = isGood . eval

hasType :: Term a -> Bool
hasType = isGood . typeOf

-- TODO: make arbitrary instances in order to use these
prop_id t = hasValue t && hasType t ==> eval t' == eval t
  where t' = app (tapp id' (get $ typeOf t)) t

prop_typed t = hasType t ==> hasValue t

