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

	def keys(self):
		return self._minpolys.keys()

	def __getitem__(self,key):
		if self.keys().count(key) == 1:
			ind = self.keys().index(key)
			key_true = self.keys()[ind]   ## keys may be equal as algebraic numbers but not equal as strings
			return self._minpolys[key_true]
		else:
			self._minpolys[key] = self.compute_minpolys(key)
			return self._minpolys[key]

	def compute_minpolys(self,key):		
		try:
			key.abs() ### HACKING HERE -- functions takes either numbers or characters; this distinguishes
			val = key

			N = val.multiplicative_order()

			ans = []
			CC = ComplexField(1000)
			R = PolynomialRing(QQ,'x')
			x = R.gen()

			## c = 0
			ans += [x]

			Phi_N = R(cyclotomic_polynomial(N))
			Phi_2N = R(cyclotomic_polynomial(2*N))
			C = 2**euler_phi(N)
			mPhi_N = C * Phi_N.substitute(x/2)
			if gcd(2,N) == 1:
				mPhi_2N = C * Phi_2N.substitute(x/2)
			else:
				mPhi_2N = C**2 * Phi_2N.substitute(x/2)

			## c = 1
			ans += [Phi_2N]
			if gcd(N,2) == 1:
				ans += [Phi_N]

			## c = 4
			ans += [mPhi_2N]
			if gcd(N,2) == 1:
				ans += [mPhi_N]

			## c = 2
			f = mPhi_N.substitute(x**2) 
			alpha = sqrt(CC(2 * exp(2*pi*I/N)))
			ans += [irred_with_root(f,alpha)]
			ans += [irred_with_root(f,-alpha)]

			## c = (3 \pm sqrt{5})/2
			K = QuadraticField(5,'r5')
			r5 = K.gen()
			c = (3 + r5) / 2
			c_c = (3 - r5) / 2
			RK = PolynomialRing(K,'x')
			x = RK.gen()
			f = (RK(Phi_N).substitute(x/c) * c**euler_phi(N)).substitute(x**2)
			f_c = (RK(Phi_N).substitute(x/c_c) * c_c**euler_phi(N)).substitute(x**2)
			alpha = sqrt(CC(c)* CC(exp(2*pi*I/N)))
			alpha_c = sqrt(CC(c_c)* CC(exp(2*pi*I/N)))
			g = irred_with_root(R(f*f_c),alpha)
			g_c = irred_with_root(R(f*f_c),alpha_c)
			h = irred_with_root(R(f*f_c),-alpha)
			h_c = irred_with_root(R(f*f_c),-alpha_c)
			ans += [g,g_c,h,h_c]

			# if gcd(N,5) != 1:
			# 	c = (3 - r5) / 2
			# 	f = (RK(Phi_N).substitute(x/c) * c**euler_phi(N)).substitute(x^2)
			# 	alpha = sqrt(CC(c)* CC(exp(2*pi*I/N)))
			# 	ans += [irred_with_root(f,alpha)]
			# 	ans += [irred_with_root(f,-alpha)]
		except AttributeError:
			chi = key
			ans = []
			ords = []
			fs = chi.order().divisors()
			for r in fs:
				for d in [1,2,3,4,5]:
					ords += [d*r/gcd(d,r),2*d*r/gcd(d,r)]
			ords = list(set(ords))
			ords.sort()
			for d in ords:
				pid = cyclotomic_polynomial(d)
				ans.append(pid)


		return list(set(ans))


	def possible_minpolys(self):
		chi = self.chi
		N = chi.modulus()
		evs = self.evs

		ans = {}
		vals = [chi(a) for a in range(1,N)]
		vals = list(set(vals))

		for a in vals:
			ans[a] = list(set([z.minpoly() for z in evs[a]]))

		return ans

	## returns all possible min polys at ell which mod p have pi as a factor
	def possible_Artin_polys(self,pi,val,p):
		R = PolynomialRing(GF(p),'x')

		polys = self[val]

		return [P for P in polys if R(P) % pi == 0]				

	def upper_bound(self):
		ans = 0
		for j in range(self.num_spaces()):
			ans += floor(self[j].dimension()/2)
		return ans


def even(f):
	v = list(f)
	v = [v[a] for a in range(len(v)) if a%2==1]
	return len(v) == v.count(0)


def irred_with_root(f,alpha):
	facts = f.factor()
	v = [pi[0].substitute(alpha).abs() for pi in facts]
	m = min(v)
	assert m < 10**(-10), "no root here"
	ind = v.index(m)

	return facts[ind][0]



