module InsertionSort

import Data.Vect
import Data.Fin
import Permutation
import PermCons
import Finite
import DecOrderNat
import LTE_Properties
import SortingWithProof

%access public export
%default total	

Smaller : Nat -> Nat -> Nat
Smaller Z n = Z
Smaller  m Z = Z
Smaller  (S m) (S n) = (S (Smaller m n))

-----------------------------------------------------------------

Min : (m: Nat) -> (n: Nat) -> Either (LTE m n) (LTE n m)
Min Z n = Left LTEZero
Min m Z = Right LTEZero
Min (S a) (S b) = case (Min a b) of
                       (Left l) => Left (LTESucc l)
                       (Right r) => Right (LTESucc r)

-----------------------------------------------------------------

insert: (k: Nat) -> (Vect n Nat) -> (Vect (S n) Nat)
insert k Nil = k :: Nil
insert k (x :: xs) = case (decMin k x) of
    (left pf) => k :: x :: xs
    (right pf) => x :: (insert k xs)

-----------------------------------------------------------------

sort : (Vect n Nat) -> (Vect n Nat)
sort [] = []
sort (x :: xs) = insert x (sort xs)

-----------------------------------------------------------------

VectMin: (n: Nat) -> (Vect n Nat) -> Nat
VectMin Z [] = Z
VectMin (S Z) [k] = k
VectMin (S (S len)) (x :: xs) = Smaller (VectMin (S len) xs) (x)

-----------------------------------------------------------------

insertHelper1 : (n : Nat) -> (a, x : Nat) -> 
                (xs : (Vect n Nat)) -> (LTE a x) ->
                (IsSorted (S n) (x :: xs) ) ->
                (IsSorted (S (S n)) (a :: x :: xs) )
                
insertHelper1 Z a x Nil pfLTE pfSort FZ = (LTE_Property1 a)
insertHelper1 Z a x Nil pfLTE pfSort (FS FZ) = pfLTE
insertHelper1 (S k) a x xs pfLTE pfSort FZ = (LTE_Property1 a)
insertHelper1 (S k) a x xs pfLTE pfSort (FS FZ) = pfLTE
insertHelper1 (S k) a x xs pfLTE pfSort (FS (FS l)) = 
    pfSort (FS l)
    
-----------------------------------------------------------------
{-
insertHelper2 : (n : Nat) -> (a, x : Nat) -> 
                (xs : (Vect n Nat)) -> (LTE x a) ->
                (IsSorted (S n) (x :: xs) ) ->
                (IsSorted (S (S n)) (x :: a :: xs) )

insertHelper2 Z a x Nil pfLTE pfSort FZ = (LTE_Property1 x)
insertHelper2 Z a x Nil pfLTE pfSort (FS FZ) = pfLTE
insertHelper2 (S k) a x xs pfLTE pfSort FZ = (LTE_Property1 x)                    
insertHelper2 (S k) a x xs pfLTE pfSort (FS FZ) = pfLTE
insertHelper2 (S k) a x (y :: xs) pfLTE pfSort (FS (FS FZ)) = 
    LTE_Property2 x a y pfLTE (pfSort (FS FZ))

insertHelper2 (S k) a x (y :: xs) pfLTE pfSort (FS (FS (FS l))) =
    pfSort (FS (FS l))    
-}        
 
-----------------------------------------------------------------

insertHelper3 : (a : Nat) -> (x : Nat) -> (LTE x a) -> 
                (IsSorted (S (S Z)) (x :: [a]) )

insertHelper3 a x pfLTE FZ = LTE_Property1 x
insertHelper3 a x pfLTE (FS FZ) = pfLTE  

-----------------------------------------------------------------

insertHelper4 : (k : Nat) -> (a, x, y : Nat) -> (xs : Vect k Nat) -> 
                (LTE x a) -> (LTE a y) -> 
                (IsSorted (S (S k)) (x :: y :: xs)) ->
                (IsSorted (S (S (S k))) (x :: a :: y :: xs))  

insertHelper4 k a x y xs pf_xa pf_ay pfSort FZ = LTE_Property1 x
insertHelper4 k a x y xs pf_xa pf_ay pfSort (FS FZ) = pf_xa
insertHelper4 k a x y xs pf_xa pf_ay pfSort (FS (FS (FZ))) = pf_ay
insertHelper4 k a x y xs pf_xa pf_ay pfSort (FS (FS (FS l))) =
    pfSort (FS (FS l))
    
-----------------------------------------------------------------

insertHelper5 : (k : Nat) -> (x, y : Nat) -> 
                (xs : Vect k Nat) -> 
                (IsSorted (S (S k)) (x :: y :: xs )) ->
                (IsSorted k xs)

insertHelper5 (S k) x y xs pfSort FZ = 
    LTE_Property1 (index FZ xs)                
    
insertHelper5 (S k) x y xs pfSort (FS l) = 
    (pfSort (FS (FS (FS l))))    
    
-----------------------------------------------------------------

insertHelper8 : (y : Nat) -> (IsSorted (S Z) [y])
insertHelper8 y FZ = LTE_Property1 y 

-----------------------------------------------------------------

insertHelper9 : (k : Nat) -> (x : Nat) -> (xs : Vect k Nat) ->
                (IsSorted (S k) (x :: xs)) -> 
                (IsSorted k xs)

insertHelper9 (S k) x xs pfSort FZ = LTE_Property1 (index FZ xs)
insertHelper9 (S k) x xs pfSort (FS l) = pfSort (FS (FS l))                 

-----------------------------------------------------------------

mutual

    insertProof : (n : Nat) -> (a : Nat) -> (xs : Vect n Nat) -> 
                  (IsSorted n xs) ->
                  (v : (Vect (S n) Nat) ** (IsSorted (S n) v) ) 

    insertHelper6 : (k : Nat) -> (a, y : Nat) -> (xs : (Vect k Nat)) ->
                    (LTE a y) -> (pf1 : (IsSorted k xs)) ->
                    (pf2 : (IsSorted (S k) (y :: xs))) -> 
                    ((y :: (fst (insertProof k a xs pf1))) = 
                     (fst (insertProof (S k) a (y :: xs) pf2)))            
                                         
    insertHelper7 : (a, y : Nat) -> (LTE a y) -> 
                    (pfS : (IsSorted (S Z) [y])) -> 
                    ((a :: [y]) = (fst (insertProof (S Z) a [y] pfS)))
    
    insertProof Z a Nil pf = ((a :: Nil) ** fun) where
        fun : (k : Fin (S Z)) -> 
              (LTE (index (pred k) (a :: Nil)) (index k (a :: Nil)))
        fun FZ = (LTE_Property1 a)
        fun (FS k) impossible

    insertProof (S Z) a (x :: Nil) pfSort = 
        case (decMin a x) of
            
            (left pfLTE) => ((a :: x :: Nil) ** 
                (insertHelper1 Z a x Nil pfLTE pfSort))
                
            (right pfLTE) => ((x :: a :: Nil) ** 
                (insertHelper3 a x pfLTE))
                
    insertHelper7 a y pfLTE pfS = ?rhs
    
    insertHelper6 Z a y Nil pfLTE pf_xs pf_yxs = ?rhs1            
            
    insertProof (S (S k)) a (x :: y :: xs) pfSort = 
        case (decMin a x) of
        
            (left pfLTE) => ((a :: x :: y :: xs ) ** 
                 (insertHelper1 (S k) a x (y :: xs) pfLTE pfSort))
             
            (right pfLTE) => case (decMin a y) of 
                (left pfLTE1) => ((x :: a :: y :: xs) ** 
                    (insertHelper4 k a x y xs pfLTE pfLTE1 pfSort))
                 
                (right pfLTE1) => let
                    v_pf = (insertProof (S k) a (y :: xs) (insertHelper9 k y xs pfSort) )  
                    v = fst v_pf
                    in
                    ( (x :: y :: v) ** ?rhs_last) 
                        
-----------------------------------------------------------------

{-
sortProof : (n : Nat) -> (Vect n Nat) -> 
            (v : (Vect n Nat) ** (IsSorted n v))
sortProof Z Nil = (Nil ** fun) where
    fun : (IsSorted Z Nil) 
    fun elem impossible
-}    
-----------------------------------------------------------------



CheckSortedVect : (n: Nat) -> (Vect n Nat) -> Bool
CheckSortedVect Z [] = True
CheckSortedVect (S Z) [k] = True
CheckSortedVect (S (S n)) (x :: xs) = case (isLTE x (VectMin (S n) xs)) of
                                         (Yes prf) => (CheckSortedVect (S n) xs)
                                         (No contra) => False
