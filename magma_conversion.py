def ps_magma_to_sage(f,chi):
	"""takes a magma power series f defined over Q(chi) and returns the corresponding Sage object"""
	Qchi = chi.base_ring()
	if Qchi == QQ:
		Qchi = CyclotomicField(2)
	z = Qchi.gen()
	R = PowerSeriesRing(Qchi,'q',default_prec=f.Degree()+1)
	q = R.gen()
	return sage_eval(str(f),locals ={'q':q,str(z):z})
		
def dc_sage_to_magma(chi):
	"""takes the Sage Dirichlet character and returns the corresponding Magma character"""
	G = chi.parent()
	N = chi.modulus()
	K = chi.base_ring()
	z = K.gen()
	M = z.multiplicative_order()
	Gm = magma.DirichletGroup(N,CyclotomicField(M))
	gens = G.unit_gens()
	vals = [magma(chi(g)) for g in gens]
	chi_m = Gm.DirichletCharacterFromValuesOnUnitGenerators(vals)
	return chi_m

def form_q_expansion_basis(chi,k,prec):
	"""finds q-expansion basis of S_k(chi)

	if global variable USE_MAGMA is true then Magma is used (but outputs sage answer)
	"""
	if not USE_MAGMA:
		return ModularSymbols(chi,k,1).cuspidal_subspace().q_expansion_basis(prec)
	else:
		chi_m = dc_sage_to_magma(chi)
		B = magma.ModularSymbols(chi_m,k,1).CuspidalSubspace().qExpansionBasis(prec)
		C = []
		for f in B:
			C += [ps_magma_to_sage(f,chi)]
		return C
