def characters_with_CM_forms(fs):
	chrs = []
	for r in range(len(fs)):
		if r%100==0:
			print "At ",r
		eps = make_character(fs[r][2],fs[r][1])
		eps = eps.minimize_base_ring()
		K = eps(1).parent()
		if K == QQ:
			K = CyclotomicField(2)
		N = K.zeta_order()
		L = CyclotomicField(N)
		Maps = Hom(K,L)
		if len(Maps)>0:
			phi = Hom(K,L)[0]
			eps = eps.change_ring(phi)
			eps = eps.minimize_base_ring()
			if chrs.count(eps)==0:
				chrs += [eps]
		else:
			print "Problem with:"
			print eps.modulus()
			print eps
			print "-------------"
		if eps.modulus()>1000:
			break

	return chrs

def form_CM_dict(fs,chrs,prec):
	CM = {}
	for eps in chrs:
		CM[eps] = []

	r = 0
	while r < len(fs):
		f,eps = make_form(fs[r])
		print eps
		if f.precision_absolute()<prec:
			print "extending:",eps
			f = extend_qexpansion(f,eps,prec)
		chi = eps.minimize_base_ring()
		K = chi(1).parent()
		if K == QQ:
			K = CyclotomicField(2)
		N = K.zeta_order()
		L = CyclotomicField(N)
		H = Hom(K,L)
		if len(H) > 0:
			phi = Hom(K,L)[0]
			chi = chi.change_ring(phi)
			chi = chi.minimize_base_ring()
			CM[chi] += [(f,eps)]
		r += 1
		if eps.modulus() > 600:
			break 

	return CM

##chi1 minimal
def compare_chars(chi1,chi2):
	K1 = chi1.base_ring()
	K2 = chi2.base_ring()
	
