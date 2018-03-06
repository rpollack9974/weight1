def full_decomposition(Ms,expected_dimension=1):
	if type(Ms) != type([1]):  ## input can be list of spaces or single space
		Ms = [Ms]
	if len(Ms) > 0:
		sturm = Ms[0].sturm_bound()
		for q in primes(sturm+1):
			max_dim = max([M.dimension() for M in Ms])
			if max_dim == expected_dimension:
				return Ms
			Ms = full_decomposition_at_prime(Ms,q)
		return Ms

def full_decomposition_at_prime(Ms,q):
	if len(Ms) == 0:
		return Ms
	elif len(Ms) > 0:
		M = Ms[0]
		Tq = M.hecke_operator(q)
		fq = Tq.charpoly()
		facts = fq.factor()
		ans = []
		for D in facts:
			f = D[0]
			e = D[1]
			ans += [((f**e).substitute(Tq)).kernel()]			
		return ans + full_decomposition_at_prime(Ms[1:len(Ms)],q)