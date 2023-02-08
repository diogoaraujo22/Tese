
{-# LANGUAGE StrictData #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}



import Data.ByteString.Char8 as BC
import Data.ByteString as B
import Cp
import FTree
import List
import Data.Bits
import ListNE
import Exp

-- | A merkle tree root.
newtype MerkleRoot a = MerkleRoot
  { getMerkleRoot :: ByteString
  } deriving (Show, Eq, Ord)

-- | A merkle tree.
data MerkleTree a
  = MerkleEmpty
  | MerkleTree Word (MerkleNode a)
  deriving (Show)

-- | A merkle node.
data MerkleNode a
  = MerkleNode (FTree (MerkleRoot a) (MerkleRoot a, a))
  deriving (Show)


k = MerkleRoot . BC.pack -- transformar uma String numa ByteString

emptyHash _ = k "" 
a = k "H4H5H6H7"
b = k "H4H5"
c = k "H6H7"
d = (k "H4", 1)--"1to2 4$")
e = (k "H5", 2)--"2to4 5$")
f = (k "H6", 3)--"5to9 2$")
g = (k "H7", 4)--"8to1 10$")

h = Comp a (Comp b (Unit d , Unit e) , Comp c (Unit f , Unit g))
mn = MerkleNode h
mt = MerkleTree 7 mn


-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------



--MT--
inMerkleTree = either (const MerkleEmpty) (uncurry MerkleTree) 
outMerkleTree(MerkleEmpty) = i1()
outMerkleTree(MerkleTree len mn) = i2(len,mn)


-- Map ---------------
mapMT f = inMerkleTree . (id -|- id >< mapMN f) . outMerkleTree 


-- toList ---------------
toListMT = (either nil (toListMN . p2)) . outMerkleTree 


-- elem ---------------
hasElemMT e = (either false (hasElemMN e . p2)) . outMerkleTree 


-- sum ---------------
sumMT = (either zero (sumMN . p2)) . outMerkleTree


-- sum ---------------
productMT = (either zero (productMN . p2)) . outMerkleTree


-- length ---------------
lengthMT = (either (const 0) p1) . outMerkleTree


-- null ---------------
nullMT = (either true false) . outMerkleTree


-- Root ---------------
rootMT = (either (emptyHash) (rootMN . p2)) . outMerkleTree


-- codigo em anexo
-- descriçao de uma operação com diagrama 
-- 




--MN--
inMerkleNode = MerkleNode 
outMerkleNode(MerkleNode ft) = ft

-- Map ---------------
mapMN f = inMerkleNode . bmap id (id >< f) . outMerkleNode


-- toList ---------------
toListMN = tl . outMerkleNode where
  tl = cataFTree (either (singl . p2) (conc . p2))


-- elem ---------------
hasElemMN e = he e . outMerkleNode where
  he e = cataFTree (either ((==e) . p2) (uncurry (||) . p2))


-- maximum ---------------
maxElemMN = me . outMerkleNode where
  me = undefined--cataFTree (either p2 (u  max . p2)) --erro pelo deriving Ord


-- minimum ---------------
minElemMN = me . outMerkleNode where
  me = undefined--cataFTree (either p2 (uncurry min . p2)) --erro pelo deriving Ord


-- sum ---------------
sumMN = se . outMerkleNode where
  se = cataFTree (either p2 (add . p2)) 


-- product ---------------
productMN = pe . outMerkleNode where
  pe = cataFTree (either p2 (mul . p2)) 


-- length ---------------
lengthMN = len . outMerkleNode where
  len = cataFTree (either one (succ . add . p2)) 


-- Root ---------------
rootMN = cataFTree (either p1 p1) . outMerkleNode





-------------------------------------------------------------------------------
-- Constructors
-------------------------------------------------------------------------------



-- | Return the largest power of two such that it's smaller than n.
powerOfTwo :: (Bits a, Num a) => a -> a
powerOfTwo n
   | n .&. (n - 1) == 0 = n `shiftR` 1
   | otherwise = go n
 where
    go w = if w .&. (w - 1) == 0 then w else go (w .&. (w - 1))

-- List to MerkleTree ---------------
mkMerkleTree =  inMerkleTree . g . outList where
  g = id -|- Cp.split (fromIntegral . Prelude.length . Cp.cons) (mkMerkleNode . Cp.cons)

-- List to MerkleNode ---------------
mkMerkleNode = inMerkleNode . list2FTree

-- List to FTree usando o criteriode partição de powerOfTwo
list2FTree = anaFTree gene where
  gene [a] = i1(MerkleRoot a,a)
  gene  x  =  let i     = (powerOfTwo . Prelude.length) x
                  (l,r) = Prelude.splitAt i x
                  mr    = (MerkleRoot . mconcat . mconcat) [l,r]
              in i2(mr,(l,r))



-- Test ----------------.
a1 = BC.pack("ola")
a2 = BC.pack("xau")
a3 = BC.pack("tb")
a4 = BC.pack("oi")
a5 = BC.pack("pau")
a6 = BC.pack("gordo")
a7 = BC.pack("fino")
a8 = BC.pack("caldo")
a9 = BC.pack("ok")
a10 = BC.pack("cs")

lista1 = [a1,a2,a3,a4,a5,a6] 
lista2 = [a1]
lista3 = [a1,a2,a3]
lista4 = [a1,a2]
lista5 = [a1,a2,a3,a4,a5,a6,a7,a8,a9,a10]




-------------------------------------------------------------------------------
-- Merkle Proofs
-------------------------------------------------------------------------------

newtype MerkleProof a = MerkleProof { getMerkleProof :: [ProofElem a] }
  deriving (Show, Eq, Ord)

data ProofElem a = ProofElem
  { nodeRoot    :: MerkleRoot a
  , siblingRoot :: MerkleRoot a
  , nodeSide    :: Side
  } deriving (Show, Eq, Ord)

data Side = L | R
  deriving (Show, Eq, Ord)


-- MerkleProof in/out ---
inMerkleProof = MerkleProof
outMerkleProof(MerkleProof l) = l


-- | Construct a merkle tree proof of inclusion
-- Walks the entire tree recursively, building a list of "proof elements"
-- that are comprised of the current node's root and it's sibling's root,
-- and whether it is the left or right sibling (this is necessary to determine
-- the order in which to hash each proof element root and it's sibling root).
-- The list is ordered such that the for each element, the next element in
-- the list is the proof element corresponding to the node's parent node.
merkleProof n = inMerkleProof . (either nil (constructPath n . p2)) . outMerkleTree 

-- constructPath utilizada na merkleProof
constructPath n = p1 . p1 . cataFTree (either g1 g2) . outMerkleNode where
      g1(mr, a) = (([], mr), Unit (mr, a))
      g2(mr,(((le,mre),fte),((ld,mrd),ftd))) | (encontra n fte) = (((ProofElem mre mrd L):le , mr) , Comp mr (fte, ftd)) 
                                             | (encontra n ftd) = (((ProofElem mrd mre R):ld , mr) , Comp mr (fte, ftd))
                                             | otherwise        = (([] , mr) , Comp mr (fte, ftd))

                                            

-- Verifica a existência de uma hash nas leafs de uma FTree
encontra n = cataFTree (either ((==n) . p1) (uncurry (||) . p2))





-- Concatena 2 MerkleRoots 
mkRootHash (MerkleRoot a) (MerkleRoot b) = MerkleRoot (a<>b)

-- Função que retorna o par (Bool b, ProofElem pe) onde b é o booleano que dita se as hashes lista de PE está correto e pe é a cabeça da lista
validateListPE leaf = cataNEList (either g1 g2) where
      g1(pe) = (nodeRoot pe == leaf , pe)
      g2(pe, (b, pep))  = let r    = nodeRoot pe
                              s    = nodeSide pep
                              rp   = nodeRoot pep
                              sibp = siblingRoot pep
                          in if (s == L) then (b && r==mkRootHash rp sibp, pe) else (b && r==mkRootHash sibp rp, pe)

-- 
validateMerkleRoot treeRoot = (==treeRoot) . (uncurry mkRootHash) . (Cp.split nodeRoot siblingRoot)

-- | Validate a merkle tree proof of inclusion
validateMerkleProof treeRoot leafRoot = uncurry (&&) . (id >< (validateMerkleRoot treeRoot)) . (validateListPE leafRoot) . outMerkleProof



-- Test ----------------.

aux1 = (k "H4")
aux2 = (k "H5")
aux3 = (k "H6")
aux4 = (k "H4H5H6H7")
aux5 = (k "H10")
mplist = merkleProof aux2 mt 

pe1 = ProofElem (k "H4H5") (k "H6H7") L
--pe2 = ProofElem (k "H4") (k "H5") L
--lista = [pe1,pe2]







{-

-- (1) Map ---------------------------------------------------------------------
 
lmap f = let a = bmap id (id >< f) in inMerkleTree . (id -|- id >< a) . outMerkleTree --bmap f g, f é aplicado a comp e g ao unit

-- (2) Length ---------------------------------------------------------------------

len = (either (const 0) p1) . outMerkleTree

-- (3) Null ---------------------------------------------------------------------

isNull = (either (const True) (const False)) . outMerkleTree

-- | Returns root of merkle tree.

mtRoot = (either emptyHash (cataFTree (either p1 p1) . p2)) . outMerkleTree 

-}
