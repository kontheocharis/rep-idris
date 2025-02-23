module Main

import Data.DPair
import Data.Fin
import Data.Void

Arity : Type
Arity = Nat

0 Each : Arity -> Type
Each = Fin

export infixr 5 :!
export infixr 5 :>
export infixr 5 :!>
export infixr 5 :*

data Tel : Type where
  Zero : Tel
  One : Tel
  (::) : (a : Type) -> (a -> Tel) -> Tel
  (:!) : (a : Type) -> (a -> Tel) -> Tel

(:>) : (a : Type) -> Tel -> Tel
a :> f = a :: (\_ => f)

(:!>) : (a : Type) -> Tel -> Tel
a :!> f = a :! (\_ => f)

Els : Tel -> Type
Els Zero = Void
Els One = ()
Els (a :: f) = DPair a (\x => Els (f x))
Els (a :! f) = Exists (\x => Els (f x))

CoEls : (t : Tel) -> (Els t -> Type) -> Type
CoEls Zero i = ()
CoEls One i = i ()
CoEls y i = (e : Els y) -> i e

apEls : {t : Tel} -> {0 u : Els t -> Type} -> CoEls t u -> (x : Els t) -> u x
apEls {t = Zero} {u} x y impossible
apEls {t = One} {u} x () = x
apEls {t = (a :: f)} x y = x y
apEls {t = (a :! f)} x y = x y

record Ctor (r : Each a) (i : Type) where
  constructor MkCtor
  args : Tel
  arity : CoEls args (const Tel)
  0 ask : CoEls args (\p => CoEls (apEls {t = args} {u = const Tel} arity p) (const i))
  0 give : CoEls args (const i)

record Data (i : Type) where
  constructor MkData
  shapes : Arity
  positions : (r : Each shapes) -> Ctor r i

0 EndCtor : Ctor r i -> (i -> Type) -> i -> Type
EndCtor (MkCtor args arity ask give) f i = DPair (Els args) (\p => (CoEls (apEls arity p) (\a => f (apEls (apEls ask p) a)), apEls give p = i))

0 End : Data i -> (i -> Type) -> i -> Type
End (MkData a c) f i = DPair (Each a) (\x => EndCtor (c x) f i)

data Mu : Data i -> i -> Type where
  In : End d (Mu d) i -> Mu d i

-- definitional eta is not supported in idris :(((((
-- 0 DispEndCtor : (d : Data i) -> (r : Each d.shapes) -> ((j : i) -> Mu d j -> Type) -> i -> Type
-- DispEndCtor (MkData a f) r m i = DPair (Els (f r).args)
--   (\p => (CoEls (apEls (f r).arity p) (\a => m (apEls (apEls (f r).ask p) a) (In (r ** (p ** ?h1)))), apEls (f r).give p = i))


-- Elimination

0 Motive : {i : Type} -> Data i -> Type
Motive d = (j : i) -> Mu d j -> Type

-- 0 Method : {i : Type} -> (d : Data i) -> CtorIdx d -> Motive d -> Type
-- Method d c m = case ctor d c of
--   MkCtor args arity ask give => ?h3

-- 0 Methods : {i : Type} -> (d : Data i) -> Motive d -> Type
-- Methods d@(MkData a f) m = (x : Each a) -> Method d (MkCtorIdx x) m

-- Vectors

VecD : (a : Type) -> Data Nat
VecD a = MkData 2 (\x => case x of
    0 => MkCtor One Zero () 0
    1 => MkCtor (a :> Nat :!> One) (const One) (\(_ ** Evidence n ()) => n) (\(_ ** Evidence n ()) => S n)
  )

data Vec : (0 a : Type) -> Nat -> Type where
  MkVec : Mu (VecD a) n -> Vec a n

nil : {0 a : Type} -> Vec a 0
nil = MkVec (In (0 ** (() ** ((), Refl))))

cons : {0 a : Type} -> {0 n : Nat} -> a -> Vec a n -> Vec a (S n)
cons {n = n} x (MkVec xs) = MkVec (In (1 ** ((x ** Evidence n ()) ** (xs, Refl))))

elimVec : {0 a : Type} -> {0 p : (n : Nat) -> Vec a n -> Type}
  -> p 0 (nil {a = a})
  -> ({0 n : Nat} -> (x : a) -> (xs : Vec a n) -> p n xs -> p (S n) (cons x xs))
  -> (0 n : Nat) -> (xs : Vec a n) -> p n xs
elimVec {a} {p} pNil pCons 0 (MkVec (In (0 ** (() ** ((), Refl))))) = pNil
elimVec {a} {p} pNil pCons (S n) (MkVec (In (1 ** ((x ** Evidence n ()) ** (xs, Refl))))) = pCons x (MkVec xs) (elimVec pNil pCons n (MkVec xs))

-- Representations

interface Repr (d : Data i) where
  R : i -> Type

  collapse : End d R j -> R j

  inspect : End d R j -> R j


-- main : IO ()
-- main = putStrLn "Hello, Idris!"





