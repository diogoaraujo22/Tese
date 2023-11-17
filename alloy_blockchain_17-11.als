--open "C:\Users\35196\OneDrive\Ambiente de Trabalho\Alloy_tese\alloy_blockchain.als"

--open alloy_blockchain 
abstract sig Bool{}

one sig True, False extends Bool{} 

-----------------------
-- Blockchain Structure
-----------------------

sig Transaction{
  	--tid : one Id 
	--hashT : one Word
}

sig Block{
    var triedNonce : set Nonce,
    var nonce : lone Nonce,
    var tx 	  : lone Tx, 
    var previous : lone Word,
    var hash  : lone Word,
    var Next   : lone Block	
}

one sig BlockI extends Block{} 

sig Nonce{
	validHash : one Bool
}

sig Tx{
	merkleRoot : one Word,
  	--transaction : set Transaction
}

sig Word{}


--------------------
-- Functions
--------------------


-- função que retorna os blocos já consolidados
fun effectiveBlocks : set Block 
	{Next.Block + Block.Next} 

-- função que retorna os blocos não consolidados
fun nonEffectiveBlocks : set Block
	{Block - effectiveBlocks} 

-- função que retorna o último bloco da cadeia
fun lastBlock : Block
	{Block-(Block.~Next)-nonEffectiveBlocks} 

-- função que retorna as nonces que produzem hashes inválidas
fun invalidNonces : set Nonce
	{{n:Nonce | n.validHash = False}} 


--------------------
-- Predicates
--------------------

-- o next de um bloco nao pode ser ele mesmo. all b : Block | b->b not in Next
pred propNoConfusionNext 
	{always no Next & iden}

-- blocos distintos não tenham o mesmo Next
pred propNoBlocksSameNext
	{always all b:effectiveBlocks | lone Next.b}

 -- a hash e o previous de um bloco nao coincidem. Esta propriedade não é necessária 
pred propNotSameHashPrev 
	{always all b : effectiveBlocks-BlockI | b.hash != b.previous}

-- blocos distintos não têm a mesma hash (hash injectivo). all b1, b2 : Block | b1!=b2 implies b1.hash != b2.hash
pred propNonSameHashBlock
	{always hash.~hash in iden}

-- se b2 é o next de b1 entao o previous de b2 coincide com a hash de b1
pred propLinkedChain
	{always Next in hash.~previous}

-- não há ciclos. all b : Block | b not in b.^Next 
pred propNoCycleChain
	{always no ^Next & iden}

-- BlockI é o bloco inicial. all bi : BlockI | no b : Block | b.Next = bi
pred propInitialBlockI
	{always no Next.BlockI}

-- todos os blocos já consolidados são alcançaveis a partir do BlockI. always all bi : BlockI, b : Block - bi | b in effectiveBlocks implies b in bi.^Next
pred propReachableFromBlockI
	{always all b : effectiveBlocks-BlockI | b in BlockI.^Next}

--os blocos não consolidados não tem previous, hash ou tx
pred propNonEffectiveBlocks
	{always no nonEffectiveBlocks.previous
 	 always no nonEffectiveBlocks.hash
 	 always no nonEffectiveBlocks.tx
	 always all b: nonEffectiveBlocks | one b.nonce}

-- bloco inicial não tem previous. --all bi : BlockI | no bi.previous
pred propNoPrevBlockI
	{always no BlockI.previous}

-- impedir isto: se b1 é o next de b0, por vezes b0.previous = b1.hash
pred propNoConfusionHashes
	{always no Next & previous.~hash}

/*
pred propM{

	-- 1st approximation
	always hash = tx.merkleRoot -- o hash de um bloco tem que coincidir com o hash das transações por forma a nao haver violação dos dados

}*/

-- Tx distintos não tem a mesma hash (merkeRoot injectivo). all tx1, tx2 : Tx | tx1!=tx2 implies tx1.merkleRoot != tx2.merkleRoot
pred propDifferentMerkleroot
	{always merkleRoot.~merkleRoot in iden}


-- a lista de transações não pode estar vazia
pred propNonEmptyTransactions{}
	--{always all tx : Tx | some tx.transaction}

-- os blocos consolidados tem obrigatoriamente previous, hash ou tx
pred propEffectiveBlocks
	{always all b: effectiveBlocks-BlockI | one b.previous
	 always all b: effectiveBlocks | one b.hash
	 --always all b: effectiveBlocks | one b.tx
	always all b: effectiveBlocks | no b.nonce
	always all b: effectiveBlocks | no b.triedNonce
	}




-------------
-- Facts
-------------

fact Facts{
	propNoConfusionNext

	propNonSameHashBlock 

	propNoBlocksSameNext

	propNoCycleChain

	propLinkedChain

	propInitialBlockI

 	propReachableFromBlockI
	
	propNonEffectiveBlocks

	propNoPrevBlockI

	propNoConfusionHashes

	--propM -- aqui dá erro

	propDifferentMerkleroot

	propNonEmptyTransactions

	propEffectiveBlocks

} 


fact Init {
	#nonEffectiveBlocks = 2
 	triedNonce = nonce
	Block.nonce.validHash in False 
	#invalidNonces = 4
}


fact Traces {
	always (nop or 
		    some b:Block, t:Tx | addBlock[b,t] or 
		    some b:Block, n:Nonce | findGoldNonce[b,n])
}

--------------------
-- Operations
--------------------

-- Add a new Block to the chain
pred addBlock [b:Block, t:Tx]{

	//guards
        	b in nonEffectiveBlocks
	t not in Block.tx
	b.nonce.validHash = True

	//effects
	previous' = previous + b->lastBlock.hash	
	hash' = hash + b->t.merkleRoot 
	tx' = tx + b->t
	Next' = Next + lastBlock->b

    	//frame conditions
	nonce' = nonce - b->b.nonce
	triedNonce' = triedNonce - b->b.triedNonce
}

-- Find a new valid nonce to miner a block
pred findGoldNonce [b:Block, n:Nonce]{

	//guards
        	b in nonEffectiveBlocks
	n not in b.triedNonce

	//effects
	triedNonce' = triedNonce + b->n
	nonce' = nonce - b->b.nonce +  b->n

    	//no frame conditions
	tx' = tx
	previous' = previous
	hash' = hash
	Next' = Next
}

-- Nothing happens
pred nop {
	nonce' = nonce
	tx' = tx
	previous' = previous
	hash' = hash
	Next' = Next
	triedNonce' = triedNonce
}

-- 		- error correction : wrong block added!

-----------
-- Run
-----------

run{

	all b : nonEffectiveBlocks | eventually b.nonce.validHash in True
	all b : Block | eventually b in effectiveBlocks
	all n : Nonce | n.validHash = False implies eventually n in Block.triedNonce 
 
} for 5 but exactly 6 Block, exactly 6 Word,  exactly 6 Nonce 


