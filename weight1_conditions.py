def ell_part(chi,ell):
	if chi.conductor().valuation(ell) > 0:
		D = chi.decomposition()
		return [chi for chi in D if chi.conductor().valuation(ell) > 0][0]
	else:
		return DirichletGroup(1)[0]

def non_ell_part(chi,ell):
	N = chi.modulus()
	N_ell = ell**N.valuation(ell)
	Nt = N / N_ell
	D = chi.decomposition()
	G = DirichletGroup(Nt,chi(1).parent())
	return prod([G(chi) for chi in D if chi.conductor().valuation(ell) == 0])



