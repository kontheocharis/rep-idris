module Flat.Lib

import Data.Fin
import Data.DPair

public export
data ProtocolKind : Type where
  Finite : ProtocolKind
  Infinite : ProtocolKind

public export
0 ProtocolSize : Type
ProtocolSize = (Nat, ProtocolKind)

public export
data Protocol : Nat -> ProtocolKind -> Type where
  Nil : Protocol 0 Finite
  WithField : (n : String) -> Protocol s k -> Protocol (S s) k
  WithArray : (n : String) -> Protocol 1 Infinite

public export
data ProtocolField : Protocol s k -> String -> Type where
  FieldHere : (0 n : String) -> ProtocolField (WithField n p) n
  FieldThere : ProtocolField p n -> ProtocolField (WithField n' p) n
  ArrayLength : (0 n : String) -> ProtocolField (WithArray n) n

public export
data ProtocolArray : Protocol s Infinite -> String -> Type where
  ArrayHere : (0 n : String) -> ProtocolArray (WithArray n) n
  ArrayThere : ProtocolArray p n -> ProtocolArray (WithField n' p) n

public export
arrayLength : ProtocolArray p n -> ProtocolField p n
arrayLength (ArrayHere n) = ArrayLength n
arrayLength (ArrayThere p) = FieldThere (arrayLength p)

public export
0 Byte : Type
Byte = Fin (power 2 8)

public export
0 Word : Type
Word = (Byte, Byte)

public export
wordAsNat : Word -> Nat
wordAsNat (x, y) = finToNat x + finToNat y * power 2 8

public export
0 Buf : Type
Buf = List Byte

public export
0 BufOf : Word -> Type
BufOf x = Subset Buf (\b => length b = wordAsNat x)

public export
data IsProtocol : Protocol s k -> Buf -> Type where
  IsNil : IsProtocol Nil []
  IsField : IsProtocol p bs -> IsProtocol (WithField n p) (l :: r :: bs)
  IsArray : {0 arr : Buf} -> (0 p : length arr = wordAsNat (l, r)) -> IsProtocol (WithArray n) (l :: r :: arr)

public export
0 BufFor : Protocol s k -> Type
BufFor p = Subset Buf (\b => IsProtocol p b)

getField' : (p : Protocol s k) -> ProtocolField p n -> (b : Buf) -> (0 w : IsProtocol p b) -> Word
getField' Nil f b q impossible
getField' (WithField n p) (FieldHere n) (l :: r :: bs) (IsField ip) = (l, r)
getField' (WithField n p) (FieldThere fp) (l :: r :: bs) (IsField ip) = getField' p fp bs ip
getField' (WithArray n) (ArrayLength n) (l :: r :: bs) (IsArray p) = (l, r)

getArray' : (p : Protocol s Infinite) -> (a : ProtocolArray p n) -> (b : Buf) -> (0 w : IsProtocol p b) -> BufOf (getField' p (arrayLength a) b w)
getArray' Nil f b q impossible
getArray' (WithField n p) (ArrayThere fp) (l :: r :: bs) (IsField ip) = getArray' p fp bs ip
getArray' (WithArray n) (ArrayHere n) (l :: r :: arr) (IsArray ip) = Element arr ip

public export
getField : {p : Protocol s k} -> (n : String) -> {auto f : ProtocolField p n} -> BufFor p -> Word
getField {p} _ {f} (Element b w) = getField' p f b w

public export
getArray : {p : Protocol s Infinite} -> (n : String) -> {auto a : ProtocolArray p n} -> (b : BufFor p) -> BufOf (getField n {f = arrayLength a} b)
getArray {p} _ {a} (Element b w) = getArray' p a b w
