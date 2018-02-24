attach("weight1_object.py")
attach("weight1_FC.py")
attach("weight1_decompose.py")
attach("weight1_forms.py")
attach("modp_space.py")
attach("magma_conversion.py")

try: 
	already_loaded == true
except NameError:
	print "loading CM dictionary"
	CM = load("DATA/CM_forms.1-600")
	attach("sage-instructions.sage")
#	print "loading Buzzard-Lauder CM database"
#	load("DATA/dihedral_forms.sage")
	already_loaded = true

FC = weight_one_FC()
# EXOTIC = {}
# EXOTIC_WO_CONJUGATES = {}
try:
	print "loading precomputed data"
	EXOTIC_WO_CONJUGATES = load("EXOTIC.sobj")
	print "extending data by galois conjugates"
	EXOTIC = extend_by_galois_conjugates(EXOTIC_WO_CONJUGATES)
except IOError:
	EXOTIC_WO_CONJUGATES = {}
	EXOTIC = {}
STURM = 20
RECURSION_LEVEL = 0
MAX_PRIME_TO_CHOOSE_TO_USE = 50
LOG_FILE = "DATA/log_file"
USE_MAGMA = True
f = open(LOG_FILE,'a')
f.write("STARTING COMPUTATION\n")
f.close()


## The global variable EXOTIC holds the data of the exotic forms computed so far.  It is used
## This data is used when oldforms are computed recursively.  
## EXOTIC is a dictionary which maps a character to 3-tuple (q-expansion, character, phi: Q(chi)-->K_f).  
## Not sure why the character is be included in this data when it itself is the key.
## Notes:
##
## 		1) When data for chi is recorded, the Galois conjugate data for all Galois conjugates of chi is recorded
##		2) When a space is eliminated for local reasons this is not recorded.

## EXOTIC_WO_CONJUGATES is a dictionary that contains all of the data of the forms computed.  It's keys 
## do not include the galois conjugate characters of the computed character spaces

## The global variable USE_MAGMA, if true, causes the programs to use Magma to compute q-expansion bases


def collect_weight_one_data(Nmin,Nmax,verbose=0):
	t = cputime()
	ans = []
	Nmin = max(2,Nmin)
	for N in range(Nmin,Nmax+1):
		G = DirichletGroup(N)
		Gs = G.galois_orbits()
		for chi in Gs:
			locally_okay = true
			for ell in prime_divisors(N):
				locally_okay = locally_okay and chi[0](-1)==-1 and not steinberg(chi[0],ell) and not bad_rps(chi[0],ell)
			if locally_okay:
				start_time = cputime(t)
				psi = chi[0].minimize_base_ring()
				out("---------------------------------------------------------")
				out("---------------------------------------------------------")
				out("Computing with "+str(psi))
				out("---------------------------------------------------------")
				out("---------------------------------------------------------")
				A = wt1(psi,verbose=verbose)
				if len(A.exotic_forms()) > 0:
					ans += [A]
					out("Saving to file")
					f = open("DATA/weight1.data",'a')
					f.write('\n'+str(A)+'\n')
					if not A.is_fully_computed():
						f.write('NOT FULLY COMPUTED: PROBABLY CM PROBLEM HERE\n')
					f.write(str(A.exotic_forms())+str('\n'))
					f.close()
					out("*******************************************************")
					out("*******************************************************")
					save(EXOTIC_WO_CONJUGATES,"EXOTIC")
				else:
					out("No exotic forms")
				out("Time: "+str(cputime(t)-start_time)+" -- Level: "+str(psi.modulus())+" -- Total time: "+str(cputime(t)))
	save(EXOTIC_WO_CONJUGATES,"EXOTIC")
	return ans




def out(str):
	if LOG_FILE != None:
		f = open(LOG_FILE,'a')
		f.write(str+'\n')
		f.close()
	print str

