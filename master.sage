attach("weight1_object.py")
attach("weight1_FC.py")
attach("weight1_decompose.py")
attach("weight1_forms.py")
attach("modp_space.py")

try: 
	already_loaded == true
except NameError:
	CM = load("DATA/CM_forms.1-600")
	attach("sage-instructions.sage")
	load("DATA/dihedral_forms.sage")
	already_loaded = true

FC = weight_one_FC()
EXOTIC = {}
EXOTIC_PURE = {}
STURM = 20

## needed for stupid CM_increase_precision function but makes loading incredibly slow

def collect_weight_one_data(Nmin,Nmax):
	t = cputime()
	ans = []
	for N in range(Nmin,Nmax+1):
		G = DirichletGroup(N)
		Gs = G.galois_orbits()
		for chi in Gs:
			psi = chi[0].minimize_base_ring()
			print "---------------------------------------------------------"
			print "Trying",psi
			A = wt1(psi,verbose=5)
			if len(A.exotic_forms()) > 0:
				ans += [A]
				print "Saving to file"
				f = open("DATA/weight1.data",'a')
				f.write('\n'+str(A)+'\n')
				if not A.is_fully_computed():
					f.write('NOT FULLY COMPUTED: PROBABLY CM PROBLEM HERE\n')
				f.write(str(A.exotic_forms())+str('\n'))
				f.close()
				print "*******************************************************"
				print ans
				print "*******************************************************"
				print EXOTIC_PURE
				save(EXOTIC_PURE,"EXOTIC")
			else:
				print "No exotic forms"
			print "Time:",cputime(t)
	return ans
