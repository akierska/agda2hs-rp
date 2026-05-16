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

myZip :: [a] -> [b] -> [(a, b)]
myZip [] _ = []
myZip _ [] = []
myZip (x : xs) (y : ys) = (x, y) : myZip xs ys

myUnzip :: [(a, b)] -> ([a], [b])
myUnzip [] = ([], [])
myUnzip ((a, b) : ps)
  = (a : fst (myUnzip ps), b : snd (myUnzip ps))

prop_sortIsSortedIsTrue :: Ord a => [a] -> Bool
prop_sortIsSortedIsTrue xs = isSorted (sort xs)

prop_sortIdempotentLemma :: Ord a => [a] -> Bool
prop_sortIdempotentLemma xs = sort (sort xs) == sort xs

prop_zipLengthLemma :: [a] -> [b] -> Bool
prop_zipLengthLemma xs ys
  = length (myZip xs ys) == min (length xs) (length ys)

