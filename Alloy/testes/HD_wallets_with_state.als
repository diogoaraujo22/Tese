-----------------------------
-- HD Wallets Structure
-----------------------------


sig PrivateKey{
	var generates : lone PublicKey
}

sig PublicKey{
	var addresses : lone BAddr

} 

sig BAddr{}

sig MasterPrivateKey{
	var creates : set PrivateKey,
	var originates : set MasterPrivateKey
}


--------------------
-- Functions
--------------------


-- função que as private keys orfas 
fun orphanPrivateKeys : set PrivateKey
	{{p : PrivateKey | no p.generates and no creates.p}} 

-- função que as public keys orfas 
fun orphanPublicKeys : set PublicKey
	{{p : PublicKey | no p.addresses and no generates.p}} 

-- função que os bitcoin addresses orfas 
fun orphanBAddr : set BAddr
	{{a : BAddr | no addresses.a}} 

--------------------
-- Predicates
--------------------


-- creates injective
pred propInjectiveCreates
	{always creates.~creates in iden}


-- originates injective
pred propInjectiveOriginate
	{always originates.~originates in iden}


-- generates injective
pred propInjectiveGenerates
	{always generates.~generates in iden}


-- addresses injective
pred propInjectiveAddresses
	{always addresses.~addresses in iden}
 
-- uma master private key não se pode gerar a ela mesma 
pred propNoConfusionOriginates
	{always no originates & iden}


-- at least one master private key
pred propAtLeastOneMasterPrivateKey
	{always some MasterPrivateKey}


-- one master private key creates at least one private key or one master private key
pred propAtLeastOnecCreatesOrOneOriginates
	{always all mpk : MasterPrivateKey | some mpk.creates or some mpk.originates}


-- no cycle in originates chain
pred propNoCycleOriginates
	{always no ^originates & iden}



fact Facts{

	--
	propInjectiveCreates

	--
	propInjectiveOriginate

	--
	propInjectiveGenerates

	--
	propInjectiveAddresses

	--
	propNoConfusionOriginates

	--
	propAtLeastOneMasterPrivateKey

	--
	propAtLeastOnecCreatesOrOneOriginates

	--
	propNoCycleOriginates

}



fact Traces {
	always (nop or 
		    some pr: PrivateKey, pu: PublicKey, a: BAddr | buildPrivateKey[pr, pu, a])
}



-- Estado Inicial
fact Init {
	#orphanPrivateKeys = 2
	#orphanPublicKeys = 2
	#orphanBAddr = 2
}


--------------------
-- Operations
--------------------

-- 
pred buildPrivateKey[privK: PrivateKey, pubK: PublicKey, a: BAddr]{

	//guards
	no privK.generates
	no pubK.addresses
	no addresses.a

	//effects
	addresses' = addresses + pubK->a
	generates' = generates + privK->pubK

    	//frame conditions
	creates' = creates
	originates' = originates

}

-- Nothing happens
pred nop {
	generates' = generates
	addresses' = addresses
	creates' = creates
	originates' = originates
}


-----------
-- Run
-----------

run{
	eventually no orphanPrivateKeys
	eventually no orphanPublicKeys
	eventually no orphanBAddr
} for 5 --but exactly 5 Block
