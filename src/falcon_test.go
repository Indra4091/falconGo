package falcon

import (
	"bufio"
	"io"
	"io/ioutil"
	"log"
	"strconv"
	"strings"
	"testing"

	kat "github.com/Indra4091/falconGo/src/internal/KAT"
	"github.com/Indra4091/falconGo/src/util"
)

var (
	firstPrivKey512, _ = GetPrivateKey(
		512,
		[]int16{1, -3, 0, 4, 0, 5, -3, -4, 4, -2, -6, 4, -2, 6, -5, 7, 7, -1, 1, 6, -2, 1, 6, -3, 3, 0, 7, 0, 3, -1, 0, 1, 0, 0, 2, 2, -7, 2, -7, -5, 1, 7, 3, 0, -3, 2, 7, -3, -8, -1, 5, 2, 5, 1, 5, -6, 2, -2, 3, 0, -9, 0, 1, 2, -11, 1, -7, 0, 5, -2, -3, 7, 4, 3, -3, 10, -1, -2, 10, 2, 8, -8, 0, -2, 6, -5, -1, 2, 0, 1, -4, 1, -6, -2, 0, 0, 2, 2, 0, 0, -7, 8, -3, 1, -9, 0, 4, -8, 2, 2, -2, -2, -6, -7, 4, 1, 0, 2, 4, 6, -2, 1, -6, -1, 0, -9, 5, 2, 0, 1, 2, -4, -3, 4, -3, 6, 2, 7, -2, -1, 2, -5, -6, 2, 6, 1, -2, 4, 10, -4, 0, 1, 2, -6, 0, 3, -2, -1, 1, 2, -4, 6, 0, -7, 2, -4, 3, 4, 0, -5, 2, -4, 0, -1, -1, -4, 3, -4, 2, -3, -2, 0, -7, 3, 5, -5, 0, 4, 1, 3, 6, 9, -1, -2, -2, 4, 1, 11, 4, -2, 5, -4, -4, 2, -1, 4, -1, 0, 0, -2, 3, 0, -4, -6, -1, -2, -1, -6, 2, 2, -1, 1, 1, -4, -9, -4, -5, -2, -3, 0, 2, 3, -1, 2, -1, 0, -4, -5, -4, -2, 0, 4, -4, -6, -2, -1, 0, -3, 0, -4, 7, 2, 1, -4, 4, 3, 6, -5, 2, 1, -2, 2, 2, 0, -4, 0, -1, -4, 5, -1, 1, -1, -3, -3, 3, 6, 2, -7, 5, -3, -2, -1, -1, 3, -2, 2, -2, -5, -5, -6, -8, 2, 0, 3, 1, 3, -7, 7, 2, -4, -4, 0, 0, -10, -1, 0, -1, 0, -9, 2, -5, 2, 4, -6, 3, -1, 5, -2, -6, -3, 1, 4, -4, 0, -3, 1, 3, -5, 4, -2, -2, -3, 9, -2, 1, -1, -3, -2, 4, 8, -1, -3, 4, 2, 3, 4, -4, 1, 7, -8, 0, 2, -2, -3, -1, 1, -5, -3, -10, -1, -5, 2, -1, 3, -1, -1, 5, -1, -5, 1, -6, -1, 1, -5, -4, -10, 3, 2, 3, 1, 6, -5, -3, 3, -9, -1, 4, -6, -2, 2, -1, 4, 2, -8, 1, 3, 2, -1, 3, -3, 3, 2, -3, -11, 4, -2, 2, 2, -4, 5, 1, 8, 1, 2, 5, -2, 3, -7, -5, -2, 0, 5, 3, -3, 3, 6, -3, -3, -4, -4, 0, 2, -2, 5, -7, 7, -1, 3, -1, -4, 3, -1, -3, 1, -3, 4, -3, 1, -1, -1, 2, 3, 2, -3, -6, -2, 5, 3, 0, -3, -2, -5, 7, 4, -3, 8, -1, 4, -3, -4, 1, 1, -1, 5, -1, 0, -1, 2, -3, -1, 0, 3, -2, 0, -2, 7, 1, -5, 5, -2, -3, 4, -5, 5, 2, -3, 0, -5, 0, -4, 0, 3, 3, -1, -5, 3, 3, 4, 2, 0, 8, 7},
		[]int16{-4, -7, 4, -2, 3, 3, -2, 4, -7, -1, -2, 6, 5, 0, -1, 5, 1, 3, -5, 7, 1, 2, -9, 5, -1, 1, 7, 3, 1, -2, 4, 0, 2, -3, 2, -4, 5, 5, -4, 0, -2, -2, -5, 3, -7, -2, 3, -3, -7, -5, 5, -3, 3, -5, -1, 0, -2, 7, 6, -2, -10, -3, 4, -2, -3, 2, -4, -1, -6, 1, 1, -6, 2, 0, 7, 3, -3, 1, -8, -3, 0, -5, -4, -3, -2, 1, 0, -3, 6, -7, 4, 2, -3, -1, 4, -7, 0, 5, -1, 3, 3, -8, -3, 1, -3, 0, -5, -2, 0, -3, 3, 1, -7, -4, 4, 3, 1, -1, -7, 1, 0, -4, -1, 2, 0, 6, 3, -3, 5, -3, -2, 5, 0, -4, 0, 2, 0, 0, -1, 2, -1, -7, 3, -1, 3, -1, -1, -7, 2, -4, -5, 9, -2, 1, 1, -8, 6, -9, 2, 2, 3, -3, 4, -3, 2, 3, -3, 2, -3, -3, -2, 1, -3, -5, -7, -4, -2, 11, 1, 0, 0, 4, 4, -3, -1, -4, 3, -2, 1, -10, 9, 4, 1, -3, 0, 2, -3, 5, 0, -8, -3, 0, -2, -1, 1, -3, 5, 1, -2, 2, 0, 2, 11, 2, -2, 1, 0, 3, 0, 8, 1, 6, -1, 1, -2, -2, -1, 8, 0, 0, -3, -1, 7, 4, -3, -6, -5, 4, 1, 1, 4, 5, -1, 0, -6, 1, -4, 2, 4, 5, 3, -1, -2, 4, 2, -8, 0, 1, -2, 1, 5, -1, -8, 6, -1, -3, 0, 5, 0, 4, -1, -4, 1, 2, 11, 1, -6, -2, -5, -4, -3, 3, 2, 4, 1, 6, 4, 4, -2, -3, -3, 3, -9, -1, 6, -2, -1, -3, 4, 1, 4, 1, 3, -8, 0, 2, 0, 3, -2, -2, -2, -7, 2, 1, -5, 0, -8, -1, -7, 2, -1, 2, 4, 6, -5, 0, -5, 1, 7, 3, -1, 8, -1, 4, -3, -5, 0, 0, -6, 0, -2, 8, -3, -9, -4, -5, 3, -5, 2, -4, -2, 1, -1, -1, -4, 2, -2, 6, -6, 3, 0, 3, -7, 4, 2, -3, -5, 3, -7, 3, -3, -2, -4, 4, 4, -3, -3, -4, 5, 0, -2, -2, 2, -2, -1, 3, -5, 1, 3, 3, -6, 2, -2, 1, -3, -7, 2, 4, 2, -4, 0, 0, 7, 1, 6, 2, 3, -3, 7, 3, 3, -4, 3, 4, 5, 0, -5, 0, -8, 0, -5, -1, 2, 4, 0, -2, 0, -3, 4, 4, 5, -3, 5, -4, 0, 1, -7, 0, 1, -1, -7, -4, -4, -5, 5, 7, 0, -3, 0, -3, -2, -6, -8, -3, -6, -1, -3, 1, -4, 2, 5, 7, 1, 2, 1, -2, -6, 1, -6, -4, 0, 7, -1, 0, 6, 3, -3, -7, 1, -5, -6, -8, -5, -1, 0, 2, 4, -8, 2, 2, -8, -3, -2, -1, 0, 4, 5, -2, 1, 3, 4, -3, -4, 6, 1, -1, -6, 2, -12, 2, 4, 2},
		[]int16{30, -32, -19, 0, -14, 46, -28, -18, 1, 19, -26, -9, 41, -47, 17, -16, 31, 17, 2, 27, 0, 15, 13, 25, -14, -2, -19, -29, -18, 19, -3, 13, 16, 48, 1, -13, -24, 3, 7, -11, 75, 18, 10, 7, 11, -25, 47, -32, -21, 18, 14, 40, 14, 8, -42, -15, -12, 20, 43, -14, 54, -24, 23, 29, -13, 46, -38, -7, -4, -29, -17, 39, 10, -6, 11, 18, -12, -23, -36, 52, 3, 5, 29, -11, 35, -34, -9, 40, -7, 26, -15, 67, -67, -2, -40, 4, 1, 38, -25, 11, 42, 36, 36, 55, -10, 13, 6, -31, 78, 43, 26, 7, 9, -11, 21, 30, -4, -6, 5, 40, 0, 21, 15, -37, 67, 13, 79, 11, 21, -21, 11, -60, -2, -6, -36, 14, 26, -2, 23, -15, -22, -18, -30, 64, 9, 10, 22, -6, -57, -13, -44, 7, 6, 8, 6, 25, 7, 21, 24, 51, -47, 9, 41, -12, -17, 26, -24, -3, 20, -20, -39, -2, 11, -13, 27, 23, 65, -81, 22, 12, -12, 1, -4, 37, 38, 5, 31, -30, 32, -4, 34, -16, 15, 28, -36, -2, 35, 45, -27, -3, 39, 16, 6, 4, 26, -13, 45, -38, 28, 24, -10, 12, 26, 13, -15, -4, -25, -31, 37, 20, -36, 77, -18, 29, 1, 28, 6, 12, -26, 53, -4, -18, 18, -9, 2, 3, -29, 2, 8, 34, 26, 5, 19, -8, 25, 10, -4, 14, 2, -2, 30, -24, 41, 9, -5, -10, 14, -9, 36, 47, 13, 19, 5, 13, -32, -16, 1, 4, 40, 33, 23, -5, 0, 25, -15, 28, 28, -28, 4, -6, -18, -10, -14, 46, -46, 37, 49, -7, -2, 21, 33, 6, -29, 7, -20, -3, -30, 45, -2, 11, 4, -1, -48, 37, 47, 0, 8, -20, 4, 9, -30, -56, -34, 10, 13, 31, -52, 39, -14, 26, -25, -13, -6, 22, 27, 18, -16, 9, 13, 10, 34, -26, 18, 9, 13, 7, 46, 14, 24, 35, -25, -2, -5, 22, 8, -7, 2, 22, -1, -1, -11, -8, 25, -13, 40, -37, 5, -24, 53, -37, 2, -31, -18, -1, -6, -10, -19, -37, -20, 15, 47, 32, 14, -6, 67, -25, 3, -7, 14, 21, 28, -14, -18, -2, 13, 8, 13, 16, -14, 85, 12, 19, 34, -11, 5, -30, -48, 5, -12, 41, 3, 56, -8, -36, -11, -6, -16, -5, 5, 27, -14, -22, -24, -9, 22, -16, 36, 31, 6, -4, -1, 7, 25, 7, 10, 12, -4, -35, 24, 13, -16, -24, -5, -31, -27, 8, 16, -14, -4, 31, 23, 9, -6, -7, -39, 32, -4, 24, -3, 0, -9, 7, -60, -13, 20, 4, -7, 9, 34, -29, 20, -25, 5, 21, 4, 8, -29, -4, -18, 51, -5, -8, -29, -5, -3, -26, 2, -33, 16, -4, 27, -6, -3, -22, -7, -5, 22, -39, -5, -8, -83, -18, -33, 14, 17, 18, 23, 1, -9, 5, -5, 35, 16, -22, 41, 19, -25, -5, -6, -14, 42, 8},
		[]int16{-25, -14, 10, 8, 28, 18, 7, 12, 34, -18, -5, 2, 12, 17, 4, -18, -30, -12, -11, -18, 27, 39, 42, 53, 55, 16, -56, -33, 9, -15, 20, -3, 6, -35, -8, 12, -2, 28, 25, 30, -38, -6, -34, -3, -14, -2, 21, -27, 32, 40, 53, -15, 18, 6, 19, -20, -33, -4, 22, 4, -5, 7, 60, 3, 21, 17, -57, -19, 7, -8, 18, -13, 9, 2, 3, -29, -7, -22, -1, -19, -18, 7, -12, 40, -2, 48, 0, 17, 0, -11, 2, -43, -19, -20, 41, 5, -30, 16, -19, 32, 33, -14, -9, 15, 14, 26, -35, -40, -31, 52, 5, 52, -11, -2, -1, 2, -12, -21, 52, 9, -2, -24, -33, -41, 29, -1, 5, 41, 33, -2, -37, 1, -34, -21, 3, 23, 2, 37, -23, -24, 14, -9, 5, -19, 0, 40, 15, -42, -26, -1, 1, 35, -3, 45, 32, 8, 43, -18, -3, -18, 6, -52, 30, -12, -24, 28, 1, -3, 8, 44, 49, 13, 33, 18, 36, -31, -37, 32, -19, 31, -13, 27, -7, 23, -43, 47, 27, -9, 45, -9, 24, 50, -6, 15, 44, -29, 2, 59, 2, 30, -4, -24, 5, -26, 14, 29, 36, 38, 66, -16, 34, -9, 31, -11, -21, 12, 2, -14, -14, 41, -22, 31, 7, 21, -45, 48, -13, -8, -41, -43, -40, -2, 19, 20, 37, -22, 54, -27, -7, 7, 10, -20, -14, -12, -26, 53, 18, 19, 15, -8, 9, 3, 10, 9, -3, -19, 3, -20, 27, 29, 43, 22, -28, -42, -44, -4, -20, -12, 10, 23, 29, -28, -32, 3, 51, 57, 21, 19, 41, -45, 7, 3, 0, -40, 40, 32, 19, 39, 5, -10, 26, 22, 14, -1, 29, 66, -49, 24, 4, 3, -29, -3, -3, 12, -42, -16, 44, 9, -3, -21, 1, -27, 33, -22, -8, 5, 27, 3, -49, 66, -23, 6, -48, 26, -27, 31, 5, 5, -29, 24, 9, 44, 53, -34, -16, 1, 69, -3, 27, -10, 10, 5, -9, 11, -9, -16, -39, -8, 20, -13, -31, -26, 23, -3, 15, -1, -7, 32, 27, -52, 14, -18, 4, 9, 1, 20, 11, 42, -4, -11, 19, 19, -28, -9, -38, -36, -6, 6, 36, 6, 37, 7, 53, -33, -25, -11, 23, -39, 39, -34, 13, -16, 11, -34, 22, -9, -14, 23, 3, 7, 15, -30, 38, -28, -6, 4, 75, 3, 33, 20, -32, -41, -36, 24, -40, 5, 14, -5, -27, -16, 33, 27, 25, 27, 19, -27, -11, -19, -38, -24, -31, -28, 2, -10, 23, 15, 42, 56, 2, -11, 24, -12, -14, -10, -26, 2, -47, 26, 13, -4, -20, -12, -12, 40, 21, -33, 13, 22, 21, 17, -26, 39, -29, 40, -11, -7, -1, 9, -1, 32, -8, 8, -9, -34, 28, 20, 1, 24, -22, -6, -33, 17, 38, -6, -12, 0, 29, -33, 56, -27, 21, -16, 12, -47, 16, 25, -61, 7, -6, -45, 0, 11, 34, 24, 30, 15, -23, -28, -24, -45, 25, -30},
	)
)

//	// Test case
//	tree1 := []complex128{complex(-0.13598924188939318, 0.14027567658429987), complex(-0.13598924188939318, -0.14027567658429987)}
//	tree2 := []complex128{complex(11898, 0), complex(11898, 0)}
//	tree3 := []complex128{complex(12692.849302403765, 0), complex(12692.849302403765, 0)}
//
//	want := []complex128{
//		complex(12692.849302403765, 0),
//		complex(12692.849302403765, 0),
//	}
//	normalizeTree(144.81253976308423, tree1, tree2, tree3)
//	if !reflect.DeepEqual(tree1, want) {
//		t.Errorf("")
//	}
//}
//

// func TestNewKeyPairFromPolys(t *testing.T) {
// 	n := 512
// 	f := util.Float64ToInt16(kat.SignKAT[n][0].Rb_f)
// 	g := util.Float64ToInt16(kat.SignKAT[n][0].Rb_g)
// 	F := util.Float64ToInt16(kat.SignKAT[n][0].Rb_F)
// 	G := util.Float64ToInt16(kat.SignKAT[n][0].Rb_G)
// 	polys := [4][]int16{f, g, F, G}
// 	priv, pub, err := NewKeyPairFromPolys(uint16(n), polys)
// 	if err != nil {
// 		t.Errorf("Error generating key pair: %v", err)
// 	}
// 	log.Printf("Private key: %v", priv)
// 	log.Printf("Public key: %v", pub)
// }

func TestGetPrivateKey(t *testing.T) {
	n := 512
	f := util.Float64ToInt16(kat.SignKAT[n][0].Rb_f)
	g := util.Float64ToInt16(kat.SignKAT[n][0].Rb_g)
	F := util.Float64ToInt16(kat.SignKAT[n][0].Rb_F)
	G := util.Float64ToInt16(kat.SignKAT[n][0].Rb_G)
	priv, err := GetPrivateKey(uint16(n), f, g, F, G)
	if err != nil {
		t.Errorf("Error generating key pair: %v", err)
	}
	log.Printf("Private key: %v", priv)
}

func TestNewPrivateKey(t *testing.T) {
	n := 16

	for i := 0; i < 10; i++ {
		priv, err := GeneratePrivateKey(uint16(n))
		if err != nil {
			t.Errorf("Error generating key pair: %v", err)
		}
		log.Printf("Private key: %v", priv)
	}
}

func TestGetPublicKey(t *testing.T) {
	pub := firstPrivKey512.GetPublicKey()
	log.Printf("Public key: %v", pub.h)
}

// below here are added
func TestNewKeyPair(t *testing.T) {
	n := 16
	for i := 10; i < 10; i++ {
		priv, pub, err := NewKeyPair(uint16(n))
		if err != nil {
			t.Errorf("Error NewKeyPair: %v", err)
		}
		log.Printf("Private key: %v\n Public key: %v", priv, pub)
	}
}

func TestHashToPointPriv(t *testing.T) {
	n := 16
	message := "message"
	var salt [SaltLen]byte
	util.RandomBytes(salt[:])
	priv, err := GeneratePrivateKey(uint16(n))

	if err != nil {
		t.Errorf("Error GeneratePrivateKey: %v", err)
	}

	hashed := priv.hashToPoint([]byte(message), salt[:])
	log.Printf("private hashed value: %f", hashed)
}

func TestHashToPointPub(t *testing.T) {
	message := "message"
	var salt [SaltLen]byte
	util.RandomBytes(salt[:])

	hashed := hashToPoint([]byte(message), salt[:])
	log.Printf("public hashed value: %v", hashed)
}

func TestBasisAndMatrix(t *testing.T) {
	n := 16
	priv, err := GeneratePrivateKey(uint16(n))
	if err != nil {
		t.Errorf("Error NewKeyPair: %v", err)
	}

	B0FFT, TFFT := basisAndMatrix(priv.f, priv.g, priv.F, priv.G)
	log.Printf("B0FFT : %v", B0FFT)
	log.Printf("TFFT : %v", TFFT)
}

/*func TestPreImage(t *testing.T) {
	n := 16
	priv, err := GeneratePrivateKey(uint16(n))
	message := "message"
	var salt [SaltLen]byte
	util.RandomBytes(salt[:])
	if err != nil {
		t.Errorf("Error NewKeyPair: %v", err)
	}
	hashed := priv.hashToPoint([]byte(message), salt[:])
	s := priv.samplePreImage(hashed)
	if len(s) < 2 {
		t.Errorf("Error PreImageSize")
	}
}*/

func ReadInts(r io.Reader) ([]int, error) {
	scanner := bufio.NewScanner(r)
	scanner.Split(bufio.ScanWords)
	var result []int
	for scanner.Scan() {
		x, err := strconv.Atoi(scanner.Text())
		if err != nil {
			return result, err
		}
		result = append(result, x)
	}
	return result, scanner.Err()
}

func TestSignVerify(t *testing.T) {
	//signature := []byte("6\x08\x8d\x0e\xc6\xc08\x13_m\x15\xf6\xfb\xfb\xb6\x80g\x15\xe1!\xa9/\t\xabd\xdaL\xa8\xf3x\xf0\x16qW\xf8\x19`j\xc4&\x8a\xe8\xb3E\xf2I\xf6\x89\xa6\x8076E\xf2q\x86\xdcl\xae\x8c\xba\xdc\x8f\xa8\x1d\xac\xa2\xfb\xafK\xb0Y\x9a\xa1\x1e^\xd1\x8c=\xe2\x03r\x8e\x9cl\xfbt\xb6\xa2\x9d*\xda\x1e\x95\xcf\xa3:Y\xed}\xf6S\xcav\t\x96\xc9\xd4\xec\xee\x96}!\xd8\xe5d\x10\x00\x00\x00\x00\x00")
	//log.Printf("help: %v\n", signature)

	f, err1 := ioutil.ReadFile("messageC.txt")
	s, err2 := ioutil.ReadFile("signatureC.txt")
	th, err3 := ioutil.ReadFile("pubkeyC.txt")

	if err1 != nil {
		t.Error("couldn't read file")
	}
	if err2 != nil {
		t.Error("couldn't read file")
	}
	if err3 != nil {
		t.Error("couldn't read file")
	}

	//pub.h = []int16{11496, 8750, 6367, 8513, 9698, 2801, 11184, 7720, 3044, 6551, 12169, 6495, 2608, 10601, 3965, 2608, 6931, 5266, 5015, 11190, 11904, 11241, 2735, 6906, 7831, 6600, 4500, 9359, 4245, 5436, 8774, 2589, 4561, 8983, 696, 8332, 4550, 1996, 2855, 7575, 2429, 2784, 869, 12283, 7148, 11327, 8000, 2406, 9422, 7003, 9693, 10658, 1286, 7617, 240, 1465, 4821, 9727, 6893, 10912, 4320, 10947, 11575, 5020, 1246, 9103, 12228, 982, 1652, 5442, 5066, 1984, 5969, 10958, 11600, 6828, 10785, 9074, 11562, 8427, 7384, 10225, 3146, 9884, 227, 10528, 6914, 7012, 11418, 618, 2344, 2442, 12118, 1590, 4659, 9, 6054, 2974, 1062, 7889, 7428, 11552, 10955, 3953, 11650, 5488, 3360, 6419, 2018, 7855, 11937, 10273, 11760, 10619, 2946, 9827, 1391, 5288, 10081, 7879, 436, 2821, 10976, 4719, 3805, 9319, 9630, 2921, 4919, 11006, 8476, 822, 3362, 6488, 3539, 2966, 9066, 11199, 3581, 6766, 9874, 5432, 8230, 1904, 10886, 9536, 650, 3017, 8013, 3273, 11999, 10043, 9288, 8661, 3001, 9709, 1944, 7455, 3436, 5174, 887, 5047, 7710, 10546, 5349, 11586, 10870, 6055, 587, 5456, 2913, 7852, 4569, 89, 11242, 6656, 7772, 5474, 11556, 1074, 5017, 8253, 6103, 11848, 4716, 6126, 4405, 5651, 6845, 369, 11740, 7603, 7746, 7584, 915, 6450, 9542, 10494, 256, 9124, 4106, 8698, 7618, 1531, 11543, 9513, 1711, 1120, 6401, 11319, 947, 7814, 4649, 7342, 10521, 1379, 7114, 4336, 6053, 6221, 1914, 3752, 8195, 10946, 5208, 1259, 11370, 6416, 5131, 5381, 8682, 7596, 8281, 2484, 11339, 11788, 7058, 5553, 2273, 6449, 608, 11847, 4196, 2901, 12045, 6603, 3256, 9934, 7986, 8114, 11513, 907, 8637, 6623, 4668, 4038, 11237, 5537, 4283, 6388, 6134, 8930, 2128, 2128, 2963, 7004, 8973, 7762, 171, 10591, 7196, 745, 2586, 2633, 10421, 8891, 3400, 4224, 2007, 4723, 10362, 2104, 8976, 722, 11441, 2652, 6325, 6241, 2988, 11748, 7855, 9040, 7088, 9407, 9770, 867, 2077, 4362, 12110, 1082, 1850, 4862, 4330, 10985, 5379, 10483, 7677, 2619, 2355, 3252, 2103, 6398, 11488, 3782, 3245, 9556, 5907, 4738, 8334, 8587, 6139, 5343, 6495, 8498, 7104, 10335, 8532, 10159, 8308, 9264, 10616, 12269, 4354, 1430, 4838, 1508, 10559, 2651, 6956, 11497, 8752, 1131, 2791, 4011, 4253, 3438, 9498, 5714, 10445, 10070, 5480, 5019, 6473, 7725, 1261, 3066, 198, 7815, 2246, 3496, 8064, 739, 5866, 5569, 11456, 2244, 668, 8395, 5445, 2772, 4408, 9293, 11014, 761, 3718, 11571, 3404, 368, 3579, 10321, 6736, 11875, 10187, 529, 280, 2368, 2568, 4932, 6205, 7260, 7792, 7205, 11919, 1381, 11963, 3502, 11363, 7457, 9950, 4892, 10373, 5957, 10007, 711, 11549, 2571, 8529, 8934, 5748, 4109, 6209, 5302, 5566, 1970, 3825, 7545, 351, 11519, 7545, 2503, 3567, 1449, 2813, 4183, 7617, 12054, 6684, 8500, 1397, 2228, 4403, 10069, 7801, 4417, 9204, 1364, 3084, 3708, 8282, 9585, 5338, 10093, 4234, 6005, 8209, 1525, 3841, 5204, 2613, 2267, 3108, 8948, 8153, 7531, 7324, 9187, 2570, 684, 4422, 5060, 8768, 11619, 3214, 707, 7175, 5379, 169, 4774, 6508, 6510, 3021, 11514, 179, 4509, 3931, 3453, 7772, 4992, 4043, 12029, 8039, 9766, 8752, 5730, 5298, 2055, 8370, 9754, 2872, 731, 9288, 2970, 315, 5281, 10632, 4920, 609, 5117, 4981, 3040, 9677, 1530, 695, 10176, 5260, 3336, 2120, 6452, 6772, 3911, 5640, 4868}
	h := []int16{}

	message := make([][]uint8, 10)
	for i := 0; i < 10; i++ {
		message[i] = make([]uint8, 0)
	}

	msgg := strings.Split(string(f), "\n")
	index := 0
	for _, l := range msgg {
		bb := strings.NewReader(l)
		scanner1 := bufio.NewScanner(bb)
		scanner1.Split(bufio.ScanWords)
		for scanner1.Scan() {
			x, err := strconv.Atoi(scanner1.Text())
			if err != nil {
				t.Error("error converting bytearray to signature")
			}
			message[index] = append(message[index], uint8(x))
		}
		index++
	}

	signature := make([][]uint8, 100)
	for i := 0; i < 100; i++ {
		signature[i] = make([]uint8, 0)
	}

	index = 0
	read_lines := strings.Split(string(s), "\n")
	for _, line := range read_lines {
		if len(signature) == 0 {
			log.Printf("index: %v\n", index)
			break
		}

		r := strings.NewReader(line)
		scanner := bufio.NewScanner(r)
		scanner.Split(bufio.ScanWords)

		for scanner.Scan() {
			x, err := strconv.Atoi(scanner.Text())
			if err != nil {
				t.Error("error converting bytearray to signature")
			}
			signature[index] = append(signature[index], uint8(x))
		}
		index++
	}

	index = 0
	total_verified := 0
	publicKey := strings.Split(string(th), "\n")
	for _, l := range publicKey {
		h = []int16{}
		bb := strings.NewReader(l)
		scanner1 := bufio.NewScanner(bb)
		scanner1.Split(bufio.ScanWords)
		for scanner1.Scan() {
			x, err := strconv.Atoi(scanner1.Text())
			if err != nil {
				t.Error("error converting bytearray to signature")
			}
			h = append(h, int16(x))
		}

		//fmt.Println("pubkey: ", pub.h)

		for i := 0; i < 10; i++ {
			var signThis []uint8
			signThis = message[i]
			//fmt.Println("message: ", message[i])

			verification := Verify(h, []byte(signThis), []byte(signature[index*10+i]))
			if verification == false {
				t.Error("Error verifying signature")
			} else {
				log.Printf("%v", verification)
				total_verified++
			}
		}

		if total_verified == 100 {
			return
		}
		/*if total_verified == 100 {
			if err := os.Truncate("signatureC.txt", 0); err != nil {
				log.Printf("Failed to truncate: %v", err)
			}

			if err := os.Truncate("pubkeyC.txt", 0); err != nil {
				log.Printf("Failed to truncate: %v", err)
			}
			return
		}*/

		index++
	}
}

func TestSignVerifyBytes(t *testing.T) {
	var input = [1722]byte{44, 232, 34, 46, 24, 223, 33, 65, 37, 226, 10, 241, 43, 176, 30, 40, 11, 228, 25, 151, 47, 137, 25, 95, 10, 48, 41, 105, 15, 125, 10, 48, 27, 19, 20, 146, 19, 151, 43, 182, 46, 128, 43, 233, 10, 175, 26, 250, 30, 151, 25, 200, 17, 148, 36, 143, 16, 149, 21, 60, 34, 70, 10, 29, 17, 209, 35, 23, 2, 184, 32, 140, 17, 198, 7, 204, 11, 39, 29, 151, 9, 125, 10, 224, 3, 101, 47, 251, 27, 236, 44, 63, 31, 64, 9, 102, 36, 206, 27, 91, 37, 221, 41, 162, 5, 6, 29, 193, 0, 240, 5, 185, 18, 213, 37, 255, 26, 237, 42, 160, 16, 224, 42, 195, 45, 55, 19, 156, 4, 222, 35, 143, 47, 196, 3, 214, 6, 116, 21, 66, 19, 202, 7, 192, 23, 81, 42, 206, 45, 80, 26, 172, 42, 33, 35, 114, 45, 42, 32, 235, 28, 216, 39, 241, 12, 74, 38, 156, 0, 227, 41, 32, 27, 2, 27, 100, 44, 154, 2, 106, 9, 40, 9, 138, 47, 86, 6, 54, 18, 51, 0, 9, 23, 166, 11, 158, 4, 38, 30, 209, 29, 4, 45, 32, 42, 203, 15, 113, 45, 130, 21, 112, 13, 32, 25, 19, 7, 226, 30, 175, 46, 161, 40, 33, 45, 240, 41, 123, 11, 130, 38, 99, 5, 111, 20, 168, 39, 97, 30, 199, 1, 180, 11, 5, 42, 224, 18, 111, 14, 221, 36, 103, 37, 158, 11, 105, 19, 55, 42, 254, 33, 28, 3, 54, 13, 34, 25, 88, 13, 211, 11, 150, 35, 106, 43, 191, 13, 253, 26, 110, 38, 146, 21, 56, 32, 38, 7, 112, 42, 134, 37, 64, 2, 138, 11, 201, 31, 77, 12, 201, 46, 223, 39, 59, 36, 72, 33, 213, 11, 185, 37, 237, 7, 152, 29, 31, 13, 108, 20, 54, 3, 119, 19, 183, 30, 30, 41, 50, 20, 229, 45, 66, 42, 118, 23, 167, 2, 75, 21, 80, 11, 97, 30, 172, 17, 217, 0, 89, 43, 234, 26, 0, 30, 92, 21, 98, 45, 36, 4, 50, 19, 153, 32, 61, 23, 215, 46, 72, 18, 108, 23, 238, 17, 53, 22, 19, 26, 189, 1, 113, 45, 220, 29, 179, 30, 66, 29, 160, 3, 147, 25, 50, 37, 70, 40, 254, 1, 0, 35, 164, 16, 10, 33, 250, 29, 194, 5, 251, 45, 23, 37, 41, 6, 175, 4, 96, 25, 1, 44, 55, 3, 179, 30, 134, 18, 41, 28, 174, 41, 25, 5, 99, 27, 202, 16, 240, 23, 165, 24, 77, 7, 122, 14, 168, 32, 3, 42, 194, 20, 88, 4, 235, 44, 106, 25, 16, 20, 11, 21, 5, 33, 234, 29, 172, 32, 89, 9, 180, 44, 75, 46, 12, 27, 146, 21, 177, 8, 225, 25, 49, 2, 96, 46, 71, 16, 100, 11, 85, 47, 13, 25, 203, 12, 184, 38, 206, 31, 50, 31, 178, 44, 249, 3, 139, 33, 189, 25, 223, 18, 60, 15, 198, 43, 229, 21, 161, 16, 187, 24, 244, 23, 246, 34, 226, 8, 80, 8, 80, 11, 147, 27, 92, 35, 13, 30, 82, 0, 171, 41, 95, 28, 28, 2, 233, 10, 26, 10, 73, 40, 181, 34, 187, 13, 72, 16, 128, 7, 215, 18, 115, 40, 122, 8, 56, 35, 16, 2, 210, 44, 177, 10, 92, 24, 181, 24, 97, 11, 172, 45, 228, 30, 175, 35, 80, 27, 176, 36, 191, 38, 42, 3, 99, 8, 29, 17, 10, 47, 78, 4, 58, 7, 58, 18, 254, 16, 234, 42, 233, 21, 3, 40, 243, 29, 253, 10, 59, 9, 51, 12, 180, 8, 55, 24, 254, 44, 224, 14, 198, 12, 173, 37, 84, 23, 19, 18, 130, 32, 142, 33, 139, 23, 251, 20, 223, 25, 95, 33, 50, 27, 192, 40, 95, 33, 84, 39, 175, 32, 116, 36, 48, 41, 120, 47, 237, 17, 2, 5, 150, 18, 230, 5, 228, 41, 63, 10, 91, 27, 44, 44, 233, 34, 48, 4, 107, 10, 231, 15, 171, 16, 157, 13, 110, 37, 26, 22, 82, 40, 205, 39, 86, 21, 104, 19, 155, 25, 73, 30, 45, 4, 237, 11, 250, 0, 198, 30, 135, 8, 198, 13, 168, 31, 128, 2, 227, 22, 234, 21, 193, 44, 192, 8, 196, 2, 156, 32, 203, 21, 69, 10, 212, 17, 56, 36, 77, 43, 6, 2, 249, 14, 134, 45, 51, 13, 76, 1, 112, 13, 251, 40, 81, 26, 80, 46, 99, 39, 203, 2, 17, 1, 24, 9, 64, 10, 8, 19, 68, 24, 61, 28, 92, 30, 112, 28, 37, 46, 143, 5, 101, 46, 187, 13, 174, 44, 99, 29, 33, 38, 222, 19, 28, 40, 133, 23, 69, 39, 23, 2, 199, 45, 29, 10, 11, 33, 81, 34, 230, 22, 116, 16, 13, 24, 65, 20, 182, 21, 190, 7, 178, 14, 241, 29, 121, 1, 95, 44, 255, 29, 121, 9, 199, 13, 239, 5, 169, 10, 253, 16, 87, 29, 193, 47, 22, 26, 28, 33, 52, 5, 117, 8, 180, 17, 51, 39, 85, 30, 121, 17, 65, 35, 244, 5, 84, 12, 12, 14, 124, 32, 90, 37, 113, 20, 218, 39, 109, 16, 138, 23, 117, 32, 17, 5, 245, 15, 1, 20, 84, 10, 53, 8, 219, 12, 36, 34, 244, 31, 217, 29, 107, 28, 156, 35, 227, 10, 10, 2, 172, 17, 70, 19, 196, 34, 64, 45, 99, 12, 142, 2, 195, 28, 7, 21, 3, 0, 169, 18, 166, 25, 108, 25, 110, 11, 205, 44, 250, 0, 179, 17, 157, 15, 91, 13, 125, 30, 92, 19, 128, 15, 203, 46, 253, 31, 103, 38, 38, 34, 48, 22, 98, 20, 178, 8, 7, 32, 178, 38, 26, 11, 56, 2, 219, 36, 72, 11, 154, 1, 59, 20, 161, 41, 136, 19, 56, 2, 97, 19, 253, 19, 117, 11, 224, 37, 205, 5, 250, 2, 183, 39, 192, 20, 140, 13, 8, 8, 72, 25, 52, 26, 116, 15, 71, 22, 8, 19, 4, 114, 108, 97, 97, 103, 113, 114, 111, 101, 114, 120, 100, 109, 104, 113, 110, 120, 115, 111, 98, 114, 121, 112, 100, 110, 113, 119, 117, 117, 114, 110, 112, 57, 1, 26, 2, 141, 57, 181, 194, 187, 190, 219, 37, 147, 126, 14, 4, 160, 143, 163, 209, 164, 53, 182, 49, 216, 106, 236, 181, 9, 221, 134, 56, 139, 6, 151, 31, 128, 77, 15, 173, 96, 26, 64, 213, 138, 60, 170, 113, 30, 142, 214, 209, 125, 220, 193, 108, 143, 48, 253, 183, 125, 65, 207, 70, 218, 186, 19, 28, 223, 82, 241, 228, 46, 171, 45, 133, 62, 216, 140, 237, 122, 20, 82, 13, 182, 85, 32, 99, 148, 151, 165, 75, 120, 99, 180, 218, 46, 147, 221, 153, 175, 240, 121, 48, 52, 209, 141, 226, 115, 75, 59, 105, 174, 76, 145, 236, 27, 35, 83, 108, 207, 154, 53, 207, 70, 39, 144, 51, 172, 241, 247, 150, 182, 144, 179, 184, 136, 57, 24, 131, 176, 46, 211, 141, 31, 163, 60, 8, 45, 111, 43, 59, 163, 247, 180, 185, 67, 159, 40, 200, 58, 198, 233, 74, 103, 145, 86, 159, 191, 167, 100, 78, 188, 178, 12, 211, 182, 246, 86, 81, 181, 144, 201, 72, 223, 6, 19, 129, 119, 249, 194, 195, 133, 199, 121, 236, 21, 130, 119, 133, 143, 37, 234, 6, 183, 235, 233, 220, 248, 90, 109, 89, 166, 191, 109, 41, 155, 6, 153, 137, 143, 103, 136, 34, 72, 216, 117, 14, 178, 124, 197, 194, 224, 180, 100, 29, 1, 74, 55, 169, 195, 107, 145, 173, 76, 92, 54, 123, 124, 137, 178, 29, 9, 15, 144, 83, 229, 246, 39, 59, 163, 7, 101, 112, 72, 215, 99, 64, 202, 243, 22, 73, 202, 4, 159, 180, 240, 215, 67, 214, 206, 230, 28, 29, 4, 129, 63, 211, 207, 226, 229, 122, 1, 19, 125, 17, 225, 41, 210, 59, 77, 254, 206, 177, 190, 29, 250, 115, 210, 190, 124, 52, 31, 143, 238, 107, 62, 230, 190, 101, 254, 185, 57, 135, 166, 215, 170, 124, 101, 11, 134, 217, 153, 13, 71, 191, 185, 96, 121, 149, 143, 218, 47, 87, 45, 52, 229, 41, 203, 65, 160, 19, 85, 49, 149, 79, 190, 236, 219, 138, 119, 221, 134, 102, 89, 250, 40, 241, 186, 177, 12, 109, 136, 174, 240, 95, 241, 5, 135, 44, 101, 59, 140, 145, 41, 18, 105, 68, 58, 1, 39, 185, 235, 205, 95, 143, 20, 151, 54, 147, 148, 105, 6, 24, 169, 123, 33, 31, 95, 202, 219, 40, 203, 101, 19, 156, 102, 206, 9, 1, 217, 36, 219, 59, 49, 90, 143, 79, 163, 6, 20, 168, 28, 95, 93, 74, 159, 134, 144, 60, 210, 236, 106, 225, 211, 107, 250, 202, 100, 31, 169, 8, 101, 230, 211, 37, 126, 40, 226, 99, 150, 41, 94, 19, 235, 1, 95, 61, 167, 85, 246, 172, 219, 122, 248, 82, 149, 52, 176, 103, 203, 68, 160, 167, 42, 154, 158, 167, 189, 31, 240, 254, 188, 14, 178, 69, 201, 237, 90, 92, 149, 35, 210, 248, 119, 183, 232, 225, 33, 222, 181, 92, 127, 74, 162, 69, 32, 72, 210, 18, 209, 126, 166, 145, 21, 175, 101, 160, 89, 110, 203, 20, 122, 232, 253, 161, 30, 8, 111, 35, 50, 249, 188, 253, 12, 71, 215, 85, 56, 196, 110, 122, 81, 246, 136, 99, 255, 51, 198, 43, 145, 97, 115, 46, 119, 250, 199, 193, 144, 245, 83, 151, 13, 130, 169, 136, 97, 89, 78, 115, 155, 164, 39, 215, 15, 7, 254, 74, 64, 201, 159, 30, 242, 217, 119, 98, 217, 45, 6, 81, 190, 172, 161, 106, 138, 34, 127, 80, 154, 218, 109, 131, 233, 13, 93, 250, 104, 94, 231, 219, 249, 14, 109, 178, 88, 88, 102, 178, 22, 226, 208, 246, 245, 51, 218, 147, 16, 255, 125, 19, 184, 179, 37, 200, 170, 20, 105, 217, 4, 137, 77, 137, 155, 168, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
	output := VerifyBytes(input)
	if output == true {
		log.Printf("BYTE VERIFICATION SUCCESSFUL")
	}

	return
}
