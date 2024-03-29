--open "C:\Users\35196\OneDrive\Ambiente de Trabalho\Alloy_tese\alloy_blockchain.als"

--open alloy_blockchain 
-----------------------------
-- Blockchain Structure
-----------------------------


sig Block{
    var triedNonce : set Nonce, -- list of tried nonce
    var nonce : lone Nonce,      -- block nonce
    var tx 	  : lone Tx,                -- list of transactions
    var previous : lone Word,    -- previous block
    var hash  : lone Word,         -- block hash
    var Next   : lone Block	          -- next block
}

one sig BlockI extends Block{} -- initial block

sig Nonce{
	validHash : one Bool  -- boolean to check if nonce produces a valid hash
}

sig Tx{
	merkleRoot : one Word -- block merkle root 
}

sig Word{}  --hash

abstract sig Bool{}

one sig True, False extends Bool{} 

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

-- função que retorna as nonces que produzem hashes válidas
fun validNonces : set Nonce
	{Nonce-invalidNonces} 

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
	 always all b: nonEffectiveBlocks | one b.nonce} --

-- bloco inicial não tem previous. --all bi : BlockI | no bi.previous
pred propNoPrevBlockI
	{always no BlockI.previous}

-- impedir isto: se b1 é o next de b0, por vezes b0.previous = b1.hash
pred propNoConfusionHashes
	{always no Next & previous.~hash}


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
	always all b: effectiveBlocks | one b.nonce-- aqui
	always all b: effectiveBlocks | no b.triedNonce--
	}

-- os blocos consolidados tem nonces validas
pred propEffectiveBlocksValidNonce
	{always effectiveBlocks.nonce.validHash = True}


-- as hashes dos blocos não coincidem com as merkleroots das transações
pred propDisjHashMerkleroot
	{always no Tx.merkleRoot & Block.hash}

-- transações distintas não têm a mesma hash (th injectivo). 
--pred propNotSameTh
	--{always th.~th in iden}



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

	propDifferentMerkleroot

	propNonEmptyTransactions

	propEffectiveBlocks

	propEffectiveBlocksValidNonce

	propDisjHashMerkleroot

--	propNotSameTh

} 

-- Estado Inicial
fact Init {

	-- 2 blocos não consolidados
	#nonEffectiveBlocks = 2 

	-- tried nonces = nonEffectiveBlocks->Nonce
	triedNonce = {b: Block, n: Nonce | b in nonEffectiveBlocks and n in b.nonce}

	--  todas as nonces de blocos não consolidados produzem hashes inválidas
	nonEffectiveBlocks.nonce.validHash in False 

	-- 4 nonces que produzem hashes inválidas
	#invalidNonces = 4

	-- 4 nonces que produzem hashes válidas
	#validNonces = 4
}


fact Traces {
	always (nop or 
		    some b:Block, t:Tx, w:Word | addBlock[b,t,w] or 
		    some b:Block, n:Nonce | findGoldNonce[b,n])
}

--------------------
-- Operations
--------------------

-- Add a new Block to the chain
pred addBlock [b:Block, t:Tx, w:Word]{

	//guards
        b in nonEffectiveBlocks
	t not in Block.tx
	b.nonce.validHash = True
	w not in (Tx.merkleRoot + Block.hash)

	//effects
	previous' = previous + b->lastBlock.hash	
	hash' = hash + b->w
	tx' = tx + b->t
	Next' = Next + lastBlock->b
	triedNonce' = triedNonce - b->b.triedNonce

    	//frame conditions
	nonce' = nonce
}

-- Find a new valid nonce to miner a block
pred findGoldNonce [b:Block, n:Nonce]{

	//guards
        b in nonEffectiveBlocks
	n not in b.triedNonce

	//effects
	triedNonce' = triedNonce + b->n
	nonce' = nonce - b->b.nonce +  b->n

    	//frame conditions
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


-----------
-- Run
-----------

run{

	all b : nonEffectiveBlocks | eventually b.nonce.validHash in True
	all b : Block | eventually b in effectiveBlocks
	all n : Nonce | n.validHash = False implies eventually n in Block.triedNonce 
 
} for 5 but exactly 6 Block, exactly 12 Word,  exactly 8 Nonce 


