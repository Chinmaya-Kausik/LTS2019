module Monoid

%access public export

||| The proof that some element is identity in the type
total
IsIdentity : (mon : Type) -> ((*) : mon -> mon -> mon) -> (e : mon) -> Type
IsIdentity mon (*) e = (a : mon) -> ((a*e) = a, (e*a) = a)

||| Given a type and a binary operation the type of proofs that the operation is associative
total
Associative : (typ : Type) -> ((*): typ -> typ -> typ) -> Type
Associative typ (*) = (a : typ) -> (b : typ) -> (c : typ) -> ((a * b) * c) = (a * (b * c))

||| Given a type and a binary operation the type of proofs that the operation is commutative
total
Commutative : (typ : Type) -> ((*) : typ -> typ -> typ) -> Type
Commutative typ (*) = (a : typ) -> (b : typ) -> (a * b) = (b * a)

||| Given a type and a binary operation the type of proofs that identity exists
total
IdentityExists : (typ : Type) -> ((*) : typ -> typ -> typ) -> Type
IdentityExists typ (*) = (e : typ ** (IsIdentity typ (*) e))
--((a : typ) -> ((a*e) = a, (e*a) = a)))

total
IsMonoid : (mon : Type) -> ((*) : mon -> mon -> mon) -> Type
IsMonoid mon (*) = (Associative mon (*), IdentityExists mon (*))

||| Gives the identity of the monoid
total
Monoid_id : (mon : Type) -> ((*) : mon -> mon -> mon) -> (IsMonoid mon (*)) 
            -> (IdentityExists mon (*))
Monoid_id mon (*) (pfAss, pfId) = pfId



||| Proves that the identity in a monoid is unique
MonIdUnique: (mon : Type) -> ((*) : mon -> mon -> mon) -> (IsMonoid mon (*))
            -> (e1: mon) -> (e2: mon) -> IsIdentity mon (*) e1 -> IsIdentity mon (*) e2 -> e1 =e2
MonIdUnique mon (*) x e1 e2 pf1 pf2 = trans (sym (fst (pf2 e1))) (snd (pf1 e2))


