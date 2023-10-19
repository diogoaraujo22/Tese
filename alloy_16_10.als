--open util/sequence[T]

-----------------------
-- Blockchain Structure
-----------------------

sig Transaction{
  	--tid : one Id
  
	--hashT : one Word
}

sig Block{
    --nonce : one Nonce,
    tx 	  : one Tx, 
    prev  : lone Word,
   	hash  : one Word,
    Next  : lone Block  	
}

one sig BlockI extends Block{} 

--sig Nonce{}

sig Tx{
	merkleRoot : one Word,
  	transaction : set Transaction
}

sig Word{}

sig Id{}


-------------
-- Predicates
-------------

pred propNoConfusionNext {

	all b : Block | b->b not in Next -- o next de um bloco nao pode ser ele mesmo

}


pred propNotSameHashPrev {
  
  all b : Block | b.hash != b.prev -- a hash e o prev de um bloco nao coincidem

}


pred propNoOrphanHashes{

	all w : Word  | w in Block.prev or w in Block.hash or w in Tx.merkleRoot-- todas as word estao associadas a um bloco ou a uma merkleRoot

}


pred propNoOrphanNonces{

	--all n : Nonce | n in Block.nonce -- todas as nonce estao associadas a um bloco

}


pred propNoOrphanTx{
	
  	all t : Tx | t in Block.tx -- todas as Tx estao associadas a um bloco
 	--all t: T | some b: Block | t.hashT in b.tx.elems.hashT
  
}


pred propNonSameHashBlock{

	all b1, b2 : Block | b1!=b2 implies b1.hash != b2.hash -- 2 blocos distintos nao tem a mesma hash

}


pred propLinkedChain{

  	Next in hash.~prev -- se b2 é o next de b1 entao o prev de b2 coincide com a hash de b1

}


pred propNoCycleChain{

	all b : Block | b not in b.^Next -- nao ha ciclos

}


pred propInitialBlockI{

	all bi : BlockI | no b : Block | b.Next = bi -- obrigar BlockI a ser o bloco inicial

}


pred propReachableFromBlockI{

	all bi : BlockI, b : Block - bi | b in bi.^Next -- obrigar a que todos os blocos sejam alcanlçaveis a partir do BlockI

}


pred propNoPrevBlockI{

	all bi : BlockI | no bi.prev -- o blocoI nao tem prev

}


pred propNoConfusionHashes{

	no Next & prev.~hash -- impedir isto: se b1 é o next de b0, por vezes b0.prev = b1.hash e nao é suposto

}


pred propM{

	--hash = tx.hashTx -- o hash de um bloco tem que coincidir com o hash das transações por forma a nao haver violação dos dados

}


pred propDifferentMerkleAndHash{
	
    no Block.hash & Tx.merkleRoot -- a Merkle Root de uma lista de transações não pode coincidir com o hash de um bloco

}


pred propDifferentMerkleroot{
	
    all tx1, tx2 : Tx | tx1!=tx2 implies tx1.merkleRoot != tx2.merkleRoot -- 2 Tx distintos nao tem a mesma hash

}


pred propNoOrphanTransactions{

	all t : Transaction | t in Tx.transaction -- todas as transações tem que estar associadas a um bloco
  
}


pred propNonEmptyTransactions{
  
  all tx : Tx | some tx.transaction -- um bloco tem que ter pelo menos 1 transacao


}


--------
-- Facts
--------

fact{

	propNoConfusionNext
  
 	propNotSameHashPrev
  
  	propNoOrphanHashes

	propNoOrphanNonces
  
  	propNoOrphanTx

	propNonSameHashBlock

 	propLinkedChain
  
  	propNoCycleChain  
  
 	propInitialBlockI
    
  	propReachableFromBlockI
  	
    propNoPrevBlockI
  
  	propNoConfusionHashes
  
  	-- hash é injetivo
  
  	-- propM
  
  	propDifferentMerkleAndHash
  
  	propDifferentMerkleroot
  
  	propNoOrphanTransactions
  
  	propNonEmptyTransactions
  
}


-------------
-- Operations
-------------

-- 		- add a new Block

-- 		- error correction : wrong block added!



------
-- Run
------

run{
	--some Next & prev.~hash  
    some Next

} for 5 but exactly 4 Block
