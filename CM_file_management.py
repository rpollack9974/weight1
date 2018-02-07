
## trying to get eps take values in some normalized form with smallest coefficient field
def normalize_character(eps):
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
		return eps,True
	else:
		print "Problem with:"
		print eps.modulus()
		print eps
		print "-------------"
		return eps,False

def act_galois_char(chi,sigma):
	chis = chi.galois_orbit()
	vals_chi = chi.values_on_gens()
	for psi in chis:
		if map(sigma,vals_chi) == list(psi.values_on_gens()):
			return psi
	assert 1==0,"failed in act_galois"

def act_galois_ps(f,sigma):
	R = f.parent()
	q = R.gen()
	ans = 0
	for n in range(f.degree()+1):
		ans += sigma(f[n]) * q**n
	return ans

def characters_with_CM_forms(fs):
	chrs = []
	for r in range(len(fs)):
		if r%100==0:
			print "At ",r
		eps = make_character(fs[r][2],fs[r][1])
		chi,bool = normalize_character(eps)
		if bool:
			if chrs.count(chi)==0:
				chrs += [chi]
		else:
			print "Problem with:"
			print eps.modulus()
			print eps
			print "-------------"
		if eps.modulus()>200:
			break

	return chrs

def form_CM_dict(fs,prec,Nmin=None,Nmax=None):
	CM = {}

	r = 0
	if Nmin == None:
		Nmin = 0
	if Nmax == None:
		Nmax = Infinity
	while r < len(fs):
		f,eps = make_form(fs[r])
		if eps.conductor() > Nmin and eps.conductor() < Nmax:
			print eps
			if f.precision_absolute()<prec:
				print "extending:",eps
				f = extend_qexpansion(f,eps,prec)
			Kf = f.base_ring()
			if Kf == QQ:
				Kf = CyclotomicField(2)
			G = Kf.galois_group()
			for sigma in G:			
				eps_sigma = act_galois_char(eps,sigma)
				print sigma,eps_sigma
				chi,bool = normalize_character(eps_sigma)
				if bool:
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
			r += 1
		if eps.modulus() > Nmax:
			break 

	return CM

##chi1 minimal
def compare_chars(chi1,chi2):
	K1 = chi1.base_ring()
	K2 = chi2.base_ring()
	
