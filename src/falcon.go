package falcon

import (
	"errors"
	"fmt"
	"math"

	"github.com/Indra4091/falconGo/src/internal"
	"github.com/Indra4091/falconGo/src/internal/transforms/fft"
	"github.com/Indra4091/falconGo/src/internal/transforms/ntt"
	"github.com/Indra4091/falconGo/src/util"

	"golang.org/x/crypto/sha3"
)

var (
	// ErrInvalidDegree is returned when the degree is not a power of 2
	ErrInvalidDegree = errors.New("n is not valid dimension/degree of the cyclotomic ring")
	// ErrInvalidPolysLenght is returned when the lenght of the polynomials is not equal to each other
	ErrInvalidPolysLength = errors.New("lenght of polynomials is not equal")
)

func isValidDegree(n uint16) bool {
	_, ok := ParamSets[n]
	return ok
}

func GetParamSet(n uint16) PublicParameters {
	if !isValidDegree(n) {
		return PublicParameters{}
	}
	return ParamSets[n]
}

func isValidPolysLength(n uint16, f, g, F, G []int16) bool {
	sum := uint16(len(f) + len(g) + len(F) + len(G))
	return sum%(4*n) == 0
}

func fft3D(polynomials [][][]float64) [][][]complex128 {
	fft3D := make([][][]complex128, len(polynomials))
	for i, row := range polynomials {
		fft3D[i] = make([][]complex128, len(row))
		for j, elt := range row {
			fft3D[i][j] = fft.FFT(elt)
		}
	}
	return fft3D
}

// From f, g, F, G, compute the basis B0 of a NTRU lattice
// as well as its Gram matrix and their fft's.
// return B0FFT, TFFT
func basisAndMatrix(f, g, F, G []int16) ([][][]complex128, internal.FFTtree) {
	B0 := [][][]float64{
		{util.Int16ToFloat64(g), fft.Neg(util.Int16ToFloat64(f))},
		{util.Int16ToFloat64(G), fft.Neg(util.Int16ToFloat64(F))},
	}
	G0 := internal.Gram(B0)
	B0FFT := fft3D(B0)
	G0FFT := fft3D(G0)
	TFFT := new(internal.FFTtree)
	TFFT.FfldlFFT(G0FFT)
	return B0FFT, *TFFT
}

// printTree prints a LDL tree in a human-readable format.
// args: a LDL tree
// Format: coefficient or fft
func printTree(tree []any, prefix string) string {
	leaf := "|_____> "
	top := "|_______"
	son1 := "|       "
	son2 := "        "
	width := len(top)
	var output string

	if len(tree) == 3 {
		if prefix == "" {
			output += prefix + fmt.Sprint(tree[0]) + "\n"
		} else {
			output += prefix[:len(prefix)-width] + top + fmt.Sprint(tree[0]) + "\n"
		}
		output += printTree(tree[1].([]any), prefix+son1)
		output += printTree(tree[2].([]any), prefix+son2)
		return output
	} else {
		return (prefix[:len(prefix)-width] + leaf + fmt.Sprint(tree) + "\n")
	}
}

// Normalize leaves of a LDLD tree (from ||b_i||**2 to sigma/||b_i||)
// args: a LDL tree (T), standar deviation (sigma)
// format: coefficient or fft
func normalizeTree(tree [][]complex128, sigma float64) {
	// python definition: normalize_tree(tree[1], sigma)
	fmt.Printf("\nnormalizeTree: sigma = %f, trees = %v", sigma, tree)
	if len(tree) == 3 {
		normalizeTree([][]complex128{tree[1], nil}, sigma)
		normalizeTree([][]complex128{tree[2], nil}, sigma)
	} else {
		tree[0][0] = complex(sigma/math.Sqrt(real(tree[0][0])), 0)
		tree[0][1] = 0
	}
}

type PublicKey struct {
	n uint16
	h []int16
}

func NewPublicKey() *PublicKey {
	return new(PublicKey)
}

func (privKey *PrivateKey) GetPublicKey() *PublicKey {
	pubKey := NewPublicKey()
	pubKey.n = privKey.n
	// a polynomial such that h*f = g mod (Phi,q)
	pubKey.h, _ = ntt.DivZq(privKey.g, privKey.f)

	return pubKey
}

type Falcon struct {
	//ParamSets
	PrivateKey
	B0FFT [][][]complex128
	TFFT  internal.FFTtree
	h     []int16
}

type PrivateKey struct {
	n uint16
	f []int16
	g []int16
	F []int16
	G []int16
}

// NewPrivateKey returns a new private key struct with empty fields.
func NewPrivateKey() *PrivateKey {
	return new(PrivateKey)
}

// GeneratePrivateKey generates a new private key.
func GeneratePrivateKey(n uint16) (*PrivateKey, error) {
	if !isValidDegree(n) {
		return nil, ErrInvalidDegree
	}
	privKey := NewPrivateKey()
	privKey.n = n
	// Compute NTRU polynomials f, g, F, G verifying fG - gF = q mod Phi
	privKey.f, privKey.g, privKey.F, privKey.G = internal.NtruGen(n)

	return privKey, nil
}

// GetPrivateKey returns a private key from the given polynomials.
func GetPrivateKey(n uint16, f, g, F, G []int16) (*PrivateKey, error) {
	if !isValidDegree(n) {
		return nil, ErrInvalidDegree
	}
	if !isValidPolysLength(n, f, g, F, G) {
		return nil, ErrInvalidPolysLength
	}
	privKey := NewPrivateKey()
	privKey.n = n
	privKey.f = f
	privKey.g = g
	privKey.F = F
	privKey.G = G

	return privKey, nil
}

// NewKeyPair generates a new keypair coresponding to the valid degree n.
func NewKeyPair(n uint16) (privKey *PrivateKey, pubKey *PublicKey, err error) {
	privKey, err = GeneratePrivateKey(n)
	if err != nil {
		return nil, nil, err
	}

	// Compute NTRU polynomials f, g, F, G verifying fG - gF = q mod Phi
	falcon := new(Falcon)
	falcon.PrivateKey = *privKey
	falcon.B0FFT, falcon.TFFT = basisAndMatrix(
		falcon.PrivateKey.f,
		falcon.PrivateKey.g,
		falcon.PrivateKey.F,
		falcon.PrivateKey.G,
	)
	normalizeTree(falcon.TFFT.AllChild(), ParamSets[n].sigma)
	falcon.h, err = ntt.DivZq(falcon.PrivateKey.g, falcon.PrivateKey.f)
	return privKey, pubKey, nil
}

func NewKeyPairFromPrivateKey(n uint16, polys [4][]int16) (privKey *PrivateKey, pubKey *PublicKey, err error) {
	falcon := new(Falcon)
	if !isValidDegree(n) {
		return nil, nil, ErrInvalidDegree
	}
	if !isValidPolysLength(n, polys[0], polys[1], polys[2], polys[3]) {
		return nil, nil, ErrInvalidPolysLength
	}

	falcon.PrivateKey.f = polys[0]
	falcon.PrivateKey.g = polys[1]
	falcon.PrivateKey.F = polys[2]
	falcon.PrivateKey.G = polys[3]

	falcon.B0FFT, falcon.TFFT = basisAndMatrix(
		falcon.PrivateKey.f,
		falcon.PrivateKey.g,
		falcon.PrivateKey.F,
		falcon.PrivateKey.G,
	)
	normalizeTree(falcon.TFFT.AllChild(), ParamSets[n].sigma)
	falcon.h, err = ntt.DivZq(falcon.PrivateKey.g, falcon.PrivateKey.f)
	return privKey, pubKey, nil
}

// Hash a message to a point in Z[x] mod(Phi, q).
// Inspired by the Parse function from NewHope.

func (privKey *PrivateKey) hashToPoint(message []byte, salt []byte) []float64 {
	if util.Q > (1 << 16) {
		panic("Q is too large")
	}

	k := (1 << 16) / util.Q
	// Create a SHAKE256 object and hash the salt and message
	shake := sha3.NewShake256()
	shake.Write(salt)
	shake.Write(message)
	// Output pseudo-random bytes and map them to coefficients
	hashed := make([]float64, privKey.n)
	i := 0
	j := 0
	for i < int(privKey.n) {
		//take two bytes, transform into int16
		//couldn't find shake.Read() definition?
		var buf [2]byte
		shake.Read(buf[:])
		// Map the bytes to coefficients
		elt := (int(buf[0]) << 8) + int(buf[1])
		// Implicit rejection sampling
		if elt < k*util.Q {
			hashed[i] = float64(elt % util.Q)
			i++
		}
		j++
	}
	return hashed
}

///////////////////////////////////////////////////////////////////////////////////
//hashToPoint but uses type PublicKey as an assiciator
//type converted from []float64 to []int16

func hashToPoint(message []byte, salt []byte) []int16 {

	n := 512
	// Create a SHAKE256 object and hash the salt and message
	shake := sha3.NewShake256()
	shake.Write(salt)
	shake.Write(message)
	// Output pseudo-random bytes and map them to coefficients
	hashed := make([]int16, n)
	i := 0

	for i < int(n) {
		//take two bytes, transform into int16
		//couldn't find shake.Read() definition?
		var buf [2]byte
		shake.Read(buf[:])
		// Map the bytes to coefficients
		elt := (int(buf[0]) << 8) | int(buf[1])
		// Implicit rejection sampling
		if elt < 61445 {
			hashed[i] = int16(elt % util.Q)
			i++
		}

	}
	return hashed
}

/*const (
	maxRate = 136
)

type inner_shake256_context struct {
	A    [25]uint64
	dbuf []uint8 //points into storage
	dptr int     // points at the current position in dbuf
}

// (reference to sha3 library)
func xorInGeneric(d *inner_shake256_context, buf []byte) {
	n := len(buf) / 8

	for i := 0; i < n; i++ {
		a := binary.LittleEndian.Uint64(buf)
		d.A[i] ^= a
		buf = buf[8:]
	}
}

// copyOutGeneric copies uint64s to a byte buffer (reference to sha3 library)
func copyOutGeneric(d *inner_shake256_context, b []byte) {
	for i := 0; len(b) >= 8; i++ {
		binary.LittleEndian.PutUint64(b, d.A[i])
		b = b[8:]
	}
}

func (sc *inner_shake256_context) shake256_init() {
	//memset(sc->st.A, 0, sizeof sc->st.A);
	sc.dptr = 0
	for j := range sc.A {
		sc.A[j] = 0
	}
}

func (d *inner_shake256_context) permute_inject() {
	xorInGeneric(d, d.dbuf)
	process_block(&d.A)
	d.dptr = 0
}

func (d *inner_shake256_context) Write(p []byte) {
	dptr := d.dptr

	for len(p) > 0 {
		if len(d.dbuf) == 0 && len(p) >= maxRate {
			// The fast path; absorb a full "rate" bytes of input and apply the permutation.
			xorInGeneric(d, p[:maxRate])
			p = p[maxRate:]
			process_block(&d.A)
			//ignores the byte buff
		} else {
			// The slow path; buffer the input until we can fill the sponge, and then xor it in.
			todo := maxRate - len(d.dbuf)
			if todo > len(p) {
				todo = len(p)
			}
			d.dbuf = append(d.dbuf, p[:todo]...)
			p = p[todo:]
			xorInGeneric(d, d.dbuf[dptr:dptr+todo])
			dptr += todo

			// If the sponge is full, apply the permutation.
			if len(d.dbuf) == maxRate {
				process_block(&d.A)
				d.dptr = 0
			}
		}
	}

	d.dptr = dptr
}

func (sc *inner_shake256_context) shake256_flip() {
	for i := sc.dptr; i < maxRate; i++ {
		sc.dbuf = append(sc.dbuf, 0)
	}
	copyOutGeneric(sc, sc.dbuf)
	//fmt.Println(sc.dbuf)
	sc.dbuf[sc.dptr] ^= 0x1F
	sc.dbuf[maxRate-1] ^= 0x80
	sc.dptr = 136
}

func (d *inner_shake256_context) Read(out *[2]byte) {

	dptr := d.dptr
	n := len(out)

	for n > 0 {
		if dptr == 136 {
			process_block(&d.A)
			copyOutGeneric(d, d.dbuf)
			dptr = 0
		}
		clen := 136 - dptr
		if clen > n {
			clen = n
		}
		n -= clen
		for i := 0; i < clen; i++ {
			out[i] = d.dbuf[dptr+i]
		}
		dptr += clen
		//d.dbuf = d.dbuf[n:]
		//out = out[n:]
	}
	d.dptr = dptr
}

func (pubKey *PublicKey) hashToPoint(message []byte, salt []byte) []int16 {

	//falcon_verify start content starts here
	var hd inner_shake256_context

	hd.shake256_init()
	fmt.Println("init clear")
	hd.Write(salt)
	fmt.Println("inject salt clear")
	hd.Write(message)
	fmt.Println("inject message clear")
	hd.shake256_flip()
	fmt.Println("flip clear")

	// Create a SHAKE256 object and hash the salt and message
	/*shake := sha3.NewShake256()
	shake.Write(salt)
	shake.Write(message)*/

// Output pseudo-random bytes and map them to coefficients
/*hashed := make([]int16, pubKey.n)
	i := 0
	for i < int(pubKey.n) {
		//take two bytes, transform into int16
		var buf [2]uint8
		hd.Read(&buf)
		// Map the bytes to coefficients
		elt := (uint32(buf[0]) << 8) | uint32(buf[1])

		// Implicit rejection sampling
		if elt < uint32(61445) {
			for elt >= 12289 {
				elt -= 12289
			}
			hashed[i] = int16(elt)
			i++
		}
	}

	return hashed
}*/
///////////////////////////////////////////////////////////////////////////////

func Verify(pubkey []int16, message []byte, signature []byte) bool {

	//fmt.Println("\nmsg: ", message)
	//fmt.Println("\nsignature as list: ", signature)
	n := 512

	salt := signature[HeadLen : HeadLen+SaltLen]
	encS := signature[HeadLen+SaltLen:]

	PubParam := GetParamSet(uint16(n))

	var normSign uint32
	normSign = 0
	//var ng uint32
	//ng = 0

	var s1 []int16
	// ss1 is dummy-array
	ss1, err := internal.Decompress(encS, int(PubParam.sigbytelen-HeadLen-SaltLen), int(n))

	/*fmt.Println("\nsigPart s1: ", ss1)*/

	if err != nil {
		fmt.Println("invalid encoding")
		return false
	}

	for i := 0; i < len(ss1); i++ {
		s1 = append(s1, int16(ss1[i]))
	}

	// compute s0 and normalize its coefficients in (-q/2, q/2]
	hashed := hashToPoint(message, salt)
	s0 := ntt.SubZq(hashed, ntt.MulZq(s1, pubkey))
	//fmt.Println("\nQ: ", util.Q)

	for i := 0; i < len(s0); i++ {
		s0[i] = int16((s0[i]+(util.Q>>1))%util.Q - (util.Q >> 1))
	}

	for _, v := range s0 {
		normSign += uint32(v) * uint32(v)
	}
	//fmt.Println("\ns0 sum: ", normSign)
	for _, v := range s1 {
		normSign += uint32(v) * uint32(v)
	}

	fmt.Println("\nsignature bound: ", PubParam.sigbound)
	fmt.Println("normSign: ", normSign)

	if normSign > PubParam.sigbound {
		return false
	}
	return true
}

//////////////////////////////////////////////////////////////////////////////

func VerifyBytes(inputBytes [1722]byte) bool {
	var pubkey []int16
	var message []byte
	var signature []byte

	j := 0

	for i := 0; i < 1024; i++ {
		var temp int16
		temp = int16(inputBytes[i]) << 8
		temp += int16(inputBytes[i+1])
		i += 1

		pubkey = append(pubkey, temp)
	}

	j = 1024

	for i := 0; i < 32; i++ {
		message = append(message, inputBytes[j+i])
	}

	j = 1024 + 32

	for i := 0; i < 666; i++ {
		signature = append(signature, inputBytes[i+j])
	}

	n := 512

	salt := signature[HeadLen : HeadLen+SaltLen]
	encS := signature[HeadLen+SaltLen:]

	PubParam := GetParamSet(uint16(n))

	var normSign uint32
	normSign = 0
	//var ng uint32
	//ng = 0

	var s1 []int16
	// ss1 is dummy-array
	ss1, err := internal.Decompress(encS, int(PubParam.sigbytelen-HeadLen-SaltLen), int(n))

	/*fmt.Println("\nsigPart s1: ", ss1)*/

	if err != nil {
		fmt.Println("invalid encoding")
		return false
	}

	for i := 0; i < len(ss1); i++ {
		s1 = append(s1, int16(ss1[i]))
	}

	// compute s0 and normalize its coefficients in (-q/2, q/2]
	hashed := hashToPoint(message, salt)
	s0 := ntt.SubZq(hashed, ntt.MulZq(s1, pubkey))
	//fmt.Println("\nQ: ", util.Q)

	for i := 0; i < len(s0); i++ {
		s0[i] = int16((s0[i]+(util.Q>>1))%util.Q - (util.Q >> 1))
	}

	for _, v := range s0 {
		normSign += uint32(v) * uint32(v)
	}
	//fmt.Println("\ns0 sum: ", normSign)
	for _, v := range s1 {
		normSign += uint32(v) * uint32(v)
	}

	fmt.Println("\nsignature bound: ", PubParam.sigbound)
	fmt.Println("normSign: ", normSign)

	if normSign > PubParam.sigbound {
		return false
	}
	return true
}
