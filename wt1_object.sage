class wt1(SageObject):

	def __init__(self,chi):
		self._neben = chi

		self._CM = []
		self._old_exotic = []

		self._upper = Infinity
		self._lower = 0

		self._spaces = []

		self._locally_constained = False
		self._bad_primes = []
		self._steinberg_primes = []
		self._bad_rps_primes = []

		self._fully_computed = False

		self.compute_space()

	def __repr__(self):
		print "Space is fully computed:",self.is_fully_computed()
		print "Space is locally constrained:",self.is_locally_constrained()
		if self.is_locally_constrained():
			print "   Steinberg primes:",self.steinberg_primes()
			print "   Bad RPS primes:",self.bad_rps_primes()
			print "   All bad primes:",self.bad_primes()
		return repr("Space of weight 1 forms with nebentype "+str(self.neben()))

	def neben(self):
		return self._neben

	def upper_bound(self):
		return self._upper

	def lower_bound(self):
		return self._lower

	def set_upper_bound(self,U):
		self._upper = U
		if self.upper_bound() == self.lower_bound():
			self.set_to_fully_computed()

	def set_lower_bound(self,L):
		self._lower = L
		if self.upper_bound() == self.lower_bound():
			self.set_to_fully_computed()

#####FUNCTIONS ABOUT SPACES FIELD
	def space(self,i):
		return self._spaces[i]

	def spaces(self):
		return self._spaces

	def set_spaces(self,spaces):
		self._spaces = spaces
		self.compute_bounds()

	def add_space(self,S):
		self._spaces += [S]

	def replace_space(self,S,i):
		self._spaces[i] = S

	def num_spaces(self):
		return len(self.spaces())

	### true if there exists a space with min polys uniquely determined
	def is_unique(self):
		unique = false
		for S in self.spaces():
			unique = unique or S.unique()
		return unique

	def unique_space(self):
		assert self.is_unique(),"no unique space here!"
		for S in self.spaces():
			if S.unique():
				return S

	### if not all minpolys are unique in any space, just return the minimum number of forms in any space
	### if there is some space with a unique min polys, then first minimal multiplicity by form across unique spaces
	def compute_upper_bound(self):
		U = min([S.num_forms() for S in self.spaces()])
		if not self.is_unique():
			self.set_upper_bound(U)
			return
		else:
			if self.num_spaces() == 0:
				self.set_upper_bound(Infinity)
				return
			else:
				T = self.unique_space()
				ans = 0
				used_forms = []
				for f in T:
					if used_forms.count(f) == 0:
						m = min([S.multiplicity(f) for S in self.spaces() if S.unique()])
						ans += m
						used_forms += [f]
				self.set_upper_bound(min(ans,U))
				return

	def has_unramified_prime(self):
		primes_used = [S.p() for S in self.spaces()]
		S = self.unique_space()
		unramified_prime = true
		for f in S:
			bool = false
			d = 1
			for q in f.primes():
				d *= f[q][0].discriminant().norm()
			for q in primes_used:
				bool = bool or d % q != 0
			unramified_prime = unramified_prime and bool
		return unramified_prime

#######################
	def CM(self):
		return self._CM

	def old_exotic(self):
		return self._old_exotic

	def add_CM(self,f):
		self._CM += [f]

	def add_old_exotic(self,f):
		self._old_exotic += [f]

	def is_fully_computed(self):
		return self._fully_computed

	def set_to_fully_computed(self):
		self._fully_computed = True

	def is_locally_constrained(self):
		return self._locally_constained

	def set_to_locally_constained(self):
		self._locally_constained = True
		self._fully_computed = True

	def bad_primes(self):
		return self._bad_primes

	def add_bad_prime(self,ell):
		self._bad_primes += [ell]

	def steinberg_primes(self):
		return self._steinberg_primes

	def add_steinberg_prime(self,ell):
		self._steinberg_primes += [ell]
		self.add_bad_prime(ell)

	### rps = ramified principal series; bad = order of character at prime > 5
	def bad_rps_primes(self):
		return self._bad_rps_primes

	def add_bad_rps_prime(self,ell):
		self._bad_rps_primes += [ell]
		self.add_bad_prime(ell)

	def compute_lower_bound(self):
		return self.set_lower_bound(len(self.CM()))

	def compute_bounds(self):
		self.compute_upper_bound()
		self.compute_lower_bound()

	def compute_space(self):
		self.check_local_constraints()
		if self.is_fully_computed():
			return

		# don't want to recursively compute old exotic here as info (of none there) might come for free
		# so we only count the number of already pre-computed forms (if any)
		self.compute_lower_bound_from_old_exotic()
		self.compute_CM()

		self.cut_down_to_unique()

		if self.is_fully_computed():
			return
		else:
			for S in self.spaces():
				print S.p()
				print S
				print "--"
			print "L:",self.lower_bound()
			print "U:",self.upper_bound()
			print self.CM()

	### checks to see:
	###		(a) whether or not nebentype is odd
	###		(b) if there are any Steinberg primes
	###		(c) if there are any bad ramified principal series primes
	def check_local_constraints(self):
		chi = self.neben()
		if chi(-1) == 1:			
			self.add_bad_prime(Infinity)
			self.set_to_locally_constained()

		N = chi.modulus()
		for ell in prime_divisors(N):
			if steinberg(chi,ell):
				self.add_steinberg_prime(ell)
				self.set_to_locally_constained()
			if bad_rps(chi,ell):
				self.add_bad_rps_prime(ell)
				self.set_to_locally_constained()

	### computes dimension of old_exotic forms from data stored in exotic -- no extra computations done
	def compute_lower_bound_from_old_exotic(self):
		chi = self.neben()
		N = chi.modulus()
		Nc = chi.conductor()
		lb = 0
		divs = divisors(N/Nc)
		divs.remove(N/Nc)  # proper divisors of N/Nc
		for d in divs:
			G_old = DirichletGroup(Nc * d)
			chi_old = G_old(chi)
			chi_old = chi_old.minimize_base_ring()
			if exotic.has_key(chi_old):
				for f in exotic[chi_old]:
					lb += multiplicity_from_oldspace(f,N)  ### chi should be contained in data of f I guess
		self.set_lower_bound(self.lower_bound()+lb)

	def compute_CM(self):
		chi = self.neben()
		N = chi.modulus()
		Nc = chi.conductor()
		
		for d in divisors(N/Nc):
			G_old = DirichletGroup(Nc * d)
			Nt = N / (Nc * d)
			chi_old = G_old(chi)
			chi_old = chi_old.minimize_base_ring()
			if CM.has_key(chi_old):
				for F in CM[chi_old]:
					f = F[0]
					chi = F[1]
					phi = F[2]
					self.add_CM(oldspan(f,N,chi,phi))  ### chi should be contained in data of f I guess

		self.compute_lower_bound()

	def primes_used(self):
		ans = []
		for S in self.spaces():
			ans += [S.p()]
		return ans

	## find non-supercuspidal prime
	def next_good_prime(self):
		chi = self.neben()
		N = chi.modulus()
		Nc = chi.conductor()
		primes_used = self.primes_used()
		if len(primes_used) == 0:
			p = 2
		else:
		    p = next_prime(max(primes_used))
		while N.valuation(p) != Nc.valuation(p):
			p = next_prime(p)

		return ZZ(p)

	def use_new_prime(self,p,log=None,verbose=False):
		sturm = STURM
		chi = self.neben()
		N = chi.modulus()

		Sp = wt1_space_modp(p,chi,verbose=verbose,log=log)
		for Sq in self.spaces():
			Sp = Sp.intersect(Sq)
		for i in range(self.num_spaces()):
			self.replace_space(self.space(i).intersect(Sp),i)
		for Sq in self.spaces():
			Sp = Sp.intersect(Sq)
		for i in range(self.num_spaces()):
			self.replace_space(self.space(i).intersect(Sp),i)
		self.add_space(Sp)
		self.compute_bounds()
		return 

	def cut_down_to_unique(self,log=None,verbose=false):
		chi = self.neben()
		sturm = STURM

		N = chi.modulus()
		Nc = chi.conductor()

		unique = false
		unramified_prime = false

		p = 1
		while (not self.is_fully_computed()) and (not self.is_unique() or not self.has_unramified_prime()):
			p = self.next_good_prime()
			self.use_new_prime(p,log=log,verbose=verbose)
		return









#--------------------
### steinberg if ell divides the level exactly onece and doesn't divide conductor of chi
def steinberg(chi,ell):
	N = chi.modulus()
	Nc = chi.conductor()
	return valuation(N/Nc,ell) == 1 and valuation(Nc,ell) == 0

### ramified principal series prime if ell divides the conductor of chi with same multiplicity as ell divides the level
### bad ramified principal series prime if ell-primary part of chi has order > 5
def bad_rps(chi,ell):
	Nc = chi.conductor()
	if Nc % ell != 0:
		return false
	D = chi.decomposition()
	for chi_ell in D:		
		if chi_ell.conductor() % ell == 0:
			break
	return chi_ell.order() > 5


def supercuspidal(chi,ell):
	N = chi.modulus()
	Nc = chi.conductor()
	return N.valuation(ell) != Nc.valuation(ell)


#----------------------------------------------------------------
## f is new in S_1(Nc * d, chi) where Nc = conductor of chi
##
## returns a list of 3-tuples.  Each 3-tuple has the form:
##
##		(h,phi,m)
##
## where 
##
## -h is a dictionary mapping ell to an eigenvalue of T_ell on
## the span of {f(d'z) : d' | N/(Nc * d) } 
## -phi is a map from Q(chi) to K_f
## -m is the multiplicity of the eigenvalue
def oldspan(f,N,chi,phi):
	print "in oldforms with",f
	Nc = chi.conductor()
	d = chi.modulus() / Nc
	L = f.base_ring()
	Qchi = chi(1).parent()
	if Qchi == QQ:
		Qchi = CyclotomicField(2)
	R = PolynomialRing(Qchi,'x')
	x = R.gen()
	Nt = N / (Nc * d)
	sturm = STURM

	h = {}
	for ell in primes(sturm):
		if N % ell != 0:
			h[ell] = f[ell]

	v = [[h,phi,1]]
	for ell in prime_divisors(N):
		new_v = []
		for t in v:
		### In this case a_ell(f) must be 0 and old copies of it still are 0
			if ell < sturm:
				if d % ell == 0:
					h = deepcopy(t[0])
					h[ell] = L(0)
					new_v += [[h,phi,t[2] * (valuation(Nt,ell) + 1)]]
			### In this case a_ell(f) persists as an eigenvalue of U_ell with mult 1 and 0 has rest of multiplicity		
				elif Nc % ell == 0:
					if valuation(Nt,ell) == 0:
						h1 = deepcopy(t[0])
						h1[ell] = f[ell]
						new_v += [[h1,phi,t[2]]]
					else:
						h2 = deepcopy(t[0])
						h2[ell] = L(0)
						new_v += [[h2,phi,t[2] * (valuation(Nt,ell))]]
				else: ## now ell must divide Nt with mult >= 2
					# P = x**2 - f[ell] * x + chi(ell)
					# M = P.splitting_field('a')
					# inc = Hom(L,M)[0]
					# P = P.change_ring(inc)
					# rs = P.roots()
					# p1 = rs[0][0].minpoly()
					# p2 = rs[1][0].minpoly()

					# h1 = deepcopy(t[0])
					# h1[ell] = [p1]
					# new_v += [[h1,t[1]]]

					# h2 = deepcopy(t[0])
					# h2[ell] = [p2]
					# new_v += [[h2,t[1]]]

					if valuation(Nt,ell) > 1:
						h3 = deepcopy(t[0])
						h3[ell] = L(0)
						new_v += [[h3,phi,t[2] * (valuation(Nt,ell)-1)]]
			else:
				new_v += [[t[0],phi,(valuation(Nt,ell) + 1)*t[2]]]
		v = new_v
	return v
