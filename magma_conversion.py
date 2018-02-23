def ps_magma_to_sage(f):
	K = f.Coefficient(0).sage().parent()
	R = PowerSeriesRing(K,'q',default_prec=f.Degree()+1)
	q = R.gen()
	z = K.gen()
	return sage_eval(str(f),locals ={'q':q,str(z):z})
		
def dc_sage_to_magma(chi):
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

def form_q_expansion_basis(chi,k,prec,use_magma=false):
	if not use_magma:
		return ModularSymbols(chi,k,1).cuspidal_subspace().q_expansion_basis(prec)
	else:
		chi_m = dc_sage_to_magma(chi)
		B = magma.ModularSymbols(chi_m,k,1).CuspidalSubspace().qExpansionBasis(prec)
		C = []
		for f in B:
			print f
			C += [ps_magma_to_sage(f)]
		return C
