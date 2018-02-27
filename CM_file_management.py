
def form_CM_dict(fs,prec,Nmax=None):
	CM = {}

	r = 0
	if Nmax == None:
		Nmax = Infinity
	while r < len(fs):
		f,eps = make_form(fs[r])
		if r % 100 == 0:
			print r,eps.modulus(),len(fs)
		N = eps.modulus()
		pass_locally = true
		for ell in prime_divisors(N):
			if steinberg(eps,ell) or bad_rps(eps,ell):
				pass_locally = false
				break
		if pass_locally and eps.modulus() < Nmax:
			if f.precision_absolute() < prec:
				f = extend_qexpansion(f,eps,prec)
			Kf = f.base_ring()
			if Kf.degree() <= 11:
				if Kf == QQ:
					Kf = CyclotomicField(2)
				G = Kf.galois_group()
				for sigma in G:			
					eps_sigma = act_galois_char(eps,sigma)
					chi = normalize_character(eps_sigma)
					if not CM.has_key(chi):
						CM[chi] = []
					K = chi(1).parent()
					if K == QQ:
						K = CyclotomicField(2)
					L = eps_sigma(1).parent()
					for phi in list(Hom(K,L)):
						if chi.change_ring(phi) == eps_sigma:
							break
					data = (act_galois_ps(f,sigma),chi,phi)
					if CM[chi].count(data) == 0:
						CM[chi] += [(act_galois_ps(f,sigma),chi,phi)]
			else:
				print "SKIPPING BECAUSE OF BIG GALOIS GROUP: ",f,eps
		r += 1
		if eps.modulus() > Nmax:
			break 

	return CM

