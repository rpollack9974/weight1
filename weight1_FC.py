from sage.structure.sage_object import SageObject

###########################################################
##  DEFINE THE HECKE EIGENVALUES OF WEIGHT 1 FORMS CLASS ##
###########################################################

######################################################################################################
##				
##  This class computes and stores the Hecke eigenvalues of weight 1 forms.  The key point is that
##  for a weight 1 eigenform f with nebentype chi, its Hecke eigenvalues at a prime ell not dividing 
##  the level N is one of the following algebraic numbers:
##
##  		sqrt(c chi(ell))
##
##  for c = 0,1,2,4.  [Buzzard-Lauder, Lemma 1]
##                                                                                               
######################################################################################################

class weight_one_FC(SageObject):
	def __init__(self):
		self._minpolys = {}
		self._pchi = {}

	def pchi(self,p,chi):
		return self._pchi[(p,chi)]

	def pchi_has_key(self,p,chi):
		return self._pchi.has_key((p,chi))

	def set_pchi(self,p,chi,pchi):
		self._pchi[(p,chi)] = pchi

	def keys(self):
		return self._minpolys.keys()

	def has_key(self,key):
		return self._minpolys.has_key(key)

	## keys (order of chi,chi(ell), chi^(ell)(ell))
	def __getitem__(self,key):
		if self.has_key(key):
			ind = self.keys().index(key)
			key_true = self.keys()[ind]   ## keys may be equal as algebraic numbers but not equal as strings
			return self._minpolys[key_true]
		else:
			self._minpolys[key] = self.compute_minpolys(key)
			return self._minpolys[key]

	def compute_minpolys(self,key):		
		ord = key[0]
		Qchi = CyclotomicField(ord)
		z = Qchi.gen()
		R = PolynomialRing(Qchi,'x')
		x = R.gen()

		if len(key) == 2:
			### at primes not dividing the level
			val = key[1]
			ans = []

			## c = 0
			ans += [x]

			## c = 1,2,4
			for c in [1,2,4]:
				f = x**2 - c * val
				facts = f.factor()
				for d in facts:
					ans += [d[0]]

			## c = (3 \pm sqrt{5})/2
			## this poly has roots sqrt((3 \pm \sqrt{5})/2) * chi(ell))
			f = x**4 - 3 * val * x**2 + val**2
			facts = f.factor()
			for d in facts:
				ans += [d[0]]
		elif len(key) == 3:
			### at primes dividing the level (Formula is a_ell^{2d} = chi^{ell}(ell)^{2d})
			non_ell_val = key[2]
			ans = []
			for d in [1,2,3,4,5]:
				f = x**(2*d) - non_ell_val**(2*d)
				facts = f.factor()
				for d in facts:
					ans += [d[0]]
		else:
			### at supercuspidal prime
			ans = [x]

		return list(set(ans))

	## returns all possible min polys at ell which mod p have g as a factor
	## care needs to be taken if ell divides the level
	##
	## galois bound given by degree Artin P must satisfy degree(P) <= [Q(a_ell):Q] / gcd([Q(a_ell):Q],[Q(chi):Q])
	def possible_Artin_polys(self,g,chi,ell,p,upper=None):
#		print "In possible with:",(g,ell,p,upper)
		N = chi.modulus()
		Nc = chi.conductor()
		Nt = N / Nc

		pchi = self.pchi(p,chi)
		kchi = pchi.residue_field()
		Qchi = chi(1).parent()
		if Qchi == QQ:
			Qchi = CyclotomicField(2)

		R = PolynomialRing(Qchi,'x')
		x = R.gen()
		Rp = PolynomialRing(kchi,'x')
		xp = Rp.gen()

		if upper == None:
			upper = Infinity

		### only doubled away from p when p \nmid N
		if ell == p and N % p !=0:
			upper *= 2

		# if chi.modulus() % ell != 0:
		# 	polys = self[(chi.order(),chi(ell))]
		# elif Nt % ell != 0:
		# 	chi_non_ell = non_ell_part(chi,ell)
		# 	polys = self[(chi.order(),chi(ell),chi_non_ell(ell))]
		# elif g == xp:
		# 	return [x]
		# else:
		# 	return []
		polys = self[make_key(chi,ell)]

		### picking polys which (a) mod p are divisible by g
		###						(b) whose degree is not so large that there will be more galois conjugates than upper
		ans = []
		for P in polys:
			# print Rp(P)
			# print g
			# print Rp(P) % g
			# print "-----"
			if Rp(P) % g == 0:
				d_ell = P.degree()
				if d_ell <= upper:
					ans += [P]
		return ans


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
	chis = [G(chi) for chi in D if chi.conductor().valuation(ell) == 0]
	if len(chis) == 0:
		return DirichletGroup(1)[0]
	else:
		return prod(chis)

def make_key(chi,ell):
	N = chi.modulus()
	Nc = chi.conductor()
	if N % ell != 0:
		return (chi.order(),chi(ell))
	elif valuation(N,ell) == valuation(Nc,ell):
		chi_non_ell = non_ell_part(chi,ell)
		return (chi.order(),chi(ell),chi_non_ell(ell))
	else:
		return (chi.order(),0,0,0)  ### hack here!
