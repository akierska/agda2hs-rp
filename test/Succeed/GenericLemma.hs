module GenericLemma where

insert :: Ord a => a -> [a] -> [a]
insert x [] = [x]
insert x (y : ys)
  = if x <= y then x : (y : ys) else y : insert x ys

sort :: Ord a => [a] -> [a]
sort [] = []
sort (x : xs) = insert x (sort xs)

isSorted :: Ord a => [a] -> Bool
isSorted [] = True
isSorted [x] = True
isSorted (x : (y : xs)) = x <= y && isSorted (y : xs)

prop_sortIsSortedIsTrue :: Ord a => [a] -> Bool
prop_sortIsSortedIsTrue xs = isSorted (sort xs)

prop_sortIdempotentLemma :: Ord a => [a] -> Bool
prop_sortIdempotentLemma xs = sort (sort xs) == sort xs

