module STLC

import Data.Vect

data Name = Const String
          | Bound Nat
          | Unquoted Nat

Eq Name where
  (==) (Const s1) (Const s2) = s1 == s2
  (==) (Bound n1) (Bound n2) = n1 == n2
  (==) (Unquoted n1) (Unquoted n2) = n1 == n2
  (==) _ _ = False

data Tipe = TPar Name | Fun Tipe Tipe

Eq Tipe where
  (==) (TPar n1) (TPar n2) = n1 == n2
  (==) (Fun t1 t2) (Fun t1' t2') = t1 == t1' && t2 == t2'
  (==) _ _ = False

infixl 8 :@:

mutual
  data TermInf : Nat -> Type where
       Ann : TermChk n -> Tipe -> TermInf n
       Var : Fin n -> TermInf n
       Par : Name -> TermInf n
       (:@:) : TermInf n -> TermChk m -> TermInf (n + m)

  data TermChk : Nat -> Type where
       Inf : TermInf n -> TermChk n
       Lam : TermChk (S n) -> TermChk n

mutual
  data Value = VLam (Value -> Value)
             | VNeutral Neutral

  data Neutral = NPar Name | NApp Neutral Value
               
vPar : Name -> Value
vPar n = VNeutral (NPar n)

data Kind = Star

data Info = HasKind Kind | HasType Tipe

Context : Type
Context = List (Name, Info)

Result : Type -> Type
Result = Either String

throw : String -> Result a
throw = Left

kindChk : Context -> Tipe -> Kind -> Result ()
kindChk gama (TPar x) Star = case lookup x gama of
                                  Just (HasKind Star) => pure ()
                                  _ => throw "unknown identifier"
kindChk gama (Fun k k') Star = do kindChk gama k Star
                                  kindChk gama k' Star

mutual
  substChk : Nat -> Nat -> TermChk d -> TermChk d
  substChk i r (Inf e) = Inf (substInf i r e)
  substChk i r (Lam e) = Lam (substChk (S i) r e)

  substInf : Nat -> Nat -> TermInf d -> TermInf d
  substInf i r (Ann e t) = Ann (substChk i r e) t
  substInf i r (Var j) = if i == finToNat j
                            then Par (Bound r)
                            else Var j
  substInf i r (Par x) = Par x
  substInf i r (e1 :@: e2) = substInf i r e1 :@: substChk i r e2

mutual
  typeInf : Nat -> Context -> TermInf d -> Result Tipe
  typeInf n gama (Ann e t) = do kindChk gama t Star
                                typeChk n gama e t
                                pure t
  typeInf _ _ (Var _) = assert_unreachable
  typeInf _ gama (Par x) = case lookup x gama of
                                Just (HasType t) => pure t
                                _ => throw "unknown identifier"
  typeInf n gama (e1 :@: e2)
    = do Fun t t' <- typeInf n gama e1 | throw "illegal application"
         typeChk n gama e2 t
         pure t'

  typeChk : Nat -> Context -> TermChk d -> Tipe -> Result ()
  typeChk n gama (Inf e) t = do t' <- typeInf n gama e
                                if t == t'
                                   then pure ()
                                   else throw "type mismatch"
  typeChk n gama (Lam e) (Fun t t')
    = typeChk (S n)
              ((Bound n, HasType t) :: gama)
              (assert_smaller (STLC.Lam e) (substChk 0 n e))
              t'
  typeChk n gama _ _ = throw "type mismatch"

typeInfZ : Context -> TermInf d -> Result Tipe
typeInfZ = typeInf Z

Env : Nat -> Type
Env n = Vect n Value

vApp : Value -> Value -> Value
vApp (VLam f)     v = f v
vApp (VNeutral n) v = VNeutral (NApp n v)

mutual
  evalInf : TermInf n -> Env (n + m) -> Value
  evalInf (Ann e _)   d = evalChk e d
  evalInf (Var i) {m} d = index (weakenN m i) d
  evalInf (Par n)     d = vPar n
  evalInf ((:@:) {n = n1} {m = n2} e1 e2) d {m}
    = vApp (evalInf {m = n2 + m} e1 (rewrite plusAssociative n1 n2 m in d))
           (evalChk {m = n1 + m} e2 (replace eqHelper d))
      where eqHelper : n1 + n2 + m = n2 + (n1 + m)
            eqHelper = rewrite plusCommutative n1 n2 in
                               sym $ plusAssociative n2 n1 m

  evalChk : TermChk n -> Env (n + m) -> Value
  evalChk (Inf i) d = evalInf i d
  evalChk (Lam e) d = VLam (\x => evalChk e (x :: d))

toFin : (j, k: Nat) -> j `LTE` k -> Fin (S k)
toFin Z k p = FZ
toFin (S j) (S k) (LTESucc p) = FS $ toFin j k p

lteMinus : j `LTE` k -> k - j `LTE` k
lteMinus {k} LTEZero = rewrite minusZeroRight k in lteRefl
lteMinus (LTESucc p) = lteSuccRight $ lteMinus p

mutual
  quote : (n: Nat) -> Value -> (d: Nat ** (TermChk d, n `LTE` d))
  quote n (VLam f)
    = let (S d ** (term, LTESucc p)) = quote (S n) (f (vPar $ Unquoted n)) in
          (d ** (Lam term, p))

  quote n (VNeutral x) = let (d ** (term, p)) = neutralQuote n x in
                             (d ** (STLC.Inf term, p))

  neutralQuote : (n: Nat) -> Neutral -> (d: Nat ** (TermInf d, n `LTE` d))
  neutralQuote n (NPar x) = varpar n x where
    varpar : (n: Nat) -> Name -> (d: Nat ** (TermInf d, n `LTE` d))
    varpar (S k) x@(Unquoted i)
      = case isLTE i k of
             Yes prf => let prf' = lteMinus prf
                            n = toFin (k - i) k prf' in
                            (S k ** (Var n, lteRefl))
             No _    => (S k ** (Par x, lteRefl))
    varpar n x = (n ** (Par x, lteRefl))
  neutralQuote n (NApp x y)
    = let (d1 ** (e1, p1)) = neutralQuote n x
          (d2 ** (e2, p2)) = quote n y in
          (d1 + d2 ** (e1 :@: e2, lteAdd p2))
    where lteAdd : n `LTE` m -> n `LTE` k + m
          lteAdd {k = Z} p = p
          lteAdd {k = (S k)} p = lteSuccRight $ lteAdd p

