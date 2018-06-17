module LambdaPi

data Name = Global String
          | Local Nat
          | Quote Nat

Eq Name where
  (Global s) == (Global s') = s == s'
  (Local n) == (Local m)    = n == m
  (Quote n) == (Quote m)    = n == m
  _ == _ = False

infixl 8 :@:

mutual
  data ITerm = Ann CTerm CTerm
             | Tipe
             | Pi CTerm CTerm
             | Bound Nat
             | Free Name
             | (:@:) ITerm CTerm

  data CTerm = Inf ITerm
             | Lam CTerm

mutual
  Eq ITerm where 
    (Ann x y) == (Ann x' y') = x == x' && y == y'
    Tipe      == Tipe        = True
    (Pi x y)  == (Pi x' y')  = x == x' && y == y'
    (Bound k) == (Bound k')  = k == k'
    (Free x)  == (Free x')   = x == x'
    (x :@: y) == (x' :@: y') = x == x' && y == y'
    _ == _ = False

  Eq CTerm where 
    (Inf x) == (Inf x') = x == x'
    (Lam x) == (Lam x') = x == x'
    _ == _ = False

mutual
  data Neutral = NFree Name
               | NApp Neutral Value

  data Value = VLam (Value -> Value)
             | VType
             | VPi Value (Value -> Value)
             | VNeutral Neutral

vFree : Name -> Value
vFree = VNeutral . NFree

vApp : Value -> Value -> Value
vApp (VLam f) v = f v
vApp VType v = assert_unreachable
vApp (VPi x f) v = assert_unreachable
vApp (VNeutral x) v = VNeutral (NApp x v)

Env : Type
Env = List Value

NameEnv : Type
NameEnv = List (Name, Value)

Gama : Type
Gama = List (Name, Value)

Result : Type -> Type
Result = Either String

fail : String -> Result a
fail = Left

%default covering

data Subst : Type where
  WithLocal : (i: Nat) -> Subst

mutual
  cSubst : Nat -> Subst -> CTerm -> CTerm
  cSubst n s (Inf x) = Inf (iSubst n s x)
  cSubst n s (Lam x) = Lam (cSubst (S n) s x)

  iSubst : Nat -> Subst -> ITerm -> ITerm
  iSubst n s (Ann x y) = Ann (cSubst n s x) (cSubst n s y)
  iSubst n s Tipe = Tipe
  iSubst n s (Pi x y) = Pi (cSubst n s x) (cSubst (S n) s y)
  iSubst n (WithLocal i) (Bound k) = if n == k then Free (Local i) else Bound k
  iSubst n s (Free x) = Free x
  iSubst n s (x :@: y) = iSubst n s x :@: cSubst n s y

mutual
  quote' : Nat -> Value -> CTerm
  quote' k (VLam f) = Lam $ quote' (S k) (f $ vFree (Quote k))
  quote' k VType = Inf Tipe
  quote' k (VPi x f) = Inf $ Pi (quote' k x) (quote' (S k) (f $ vFree (Quote k)))
  quote' k (VNeutral x) = Inf $ neutralQuote k x

  neutralQuote : Nat -> Neutral -> ITerm
  neutralQuote k (NFree x) = boundFree k x where
    boundFree : Nat -> Name -> ITerm
    boundFree k (Quote n) = Bound ((k `minus` n) `minus` 1)
    boundFree k x = Free x
  neutralQuote k (NApp x y) = neutralQuote k x :@: quote' k y

quote : Value -> CTerm
quote = quote' 0

mutual
  iEval : ITerm -> Env -> NameEnv -> Value
  iEval (Ann t _) e ne = cEval t e ne
  iEval Tipe      _ _  = VType
  iEval (Pi t t') e ne = VPi (cEval t e ne) (\x => cEval t' (x::e) ne)
  iEval (Bound k) e _ 
    = case index' k e of
           Nothing => idris_crash "index out of range"
           Just v  => v
  iEval (Free x)  _ ne
    = case lookup x ne of
           Nothing => vFree x
           Just v  => v
  iEval (x :@: y) e ne = vApp (iEval x e ne) (cEval y e ne)

  cEval : CTerm -> Env -> NameEnv -> Value
  cEval (Inf t) e ne = iEval t e ne
  cEval (Lam t) e ne = VLam (\x => cEval t (x::e) ne)
  
  iType : Nat -> NameEnv -> Gama -> ITerm -> Result Value
  iType i ne gam (Ann x t)
    = do cType i ne gam t VType
         let ty = cEval t [] ne
         cType i ne gam x ty
         pure ty
  iType i ne gam Tipe = pure VType
  iType i ne gam (Pi t t')
    = do cType i ne gam t VType
         let ty = cEval t [] ne
         cType (S i)
               ne
               ((Local i, ty)::gam)
               (cSubst 0 (WithLocal i) t')
               VType
         pure VType
  iType i ne gam (Bound _) = assert_unreachable
  iType i ne gam (Free x)
    = case lookup x gam of
           Just ty => pure ty
           Nothing => fail "unknown identifier"
  iType i ne gam (x :@: y)
    = do VPi ty ty' <- iType i ne gam x | fail "illegal application"
         cType i ne gam y ty
         pure $ ty' (cEval y [] ne)

  cType : Nat -> NameEnv -> Gama -> CTerm -> Value -> Result ()
  cType i ne gam (Inf x) v
    = do v' <- iType i ne gam x
         if quote v == quote v'
            then pure ()
            else fail "type mismatch"
  cType i ne gam (Lam x) (VPi t t')
    = cType (S i)
            ne
            ((Local i, t)::gam)
            (cSubst 0 (WithLocal i) x)
            (t' $ vFree (Local i))
  cType _ _ _ _ _ = fail "type mismatch"
