package falcon

import (
	"bufio"
	"fmt"
	"io"
	"io/ioutil"
	"log"
	"strconv"
	"strings"
	"testing"

	kat "github.com/realForbis/go-falcon-WIP/src/internal/KAT"
	"github.com/realForbis/go-falcon-WIP/src/util"
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
	n := 16
	message := "message"
	var salt [SaltLen]byte
	util.RandomBytes(salt[:])
	priv, err := GeneratePrivateKey(uint16(n))

	if err != nil {
		t.Errorf("Error GeneratePrivateKey: %v", err)
	}

	pub := priv.GetPublicKey()

	hashed := pub.hashToPoint([]byte(message), salt[:])
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

	f, err1 := ioutil.ReadFile("message.txt")
	s, err2 := ioutil.ReadFile("signature.txt")

	if err1 != nil {
		t.Error("couldn't read file")
	}
	if err2 != nil {
		t.Error("couldn't read file")
	}

	n := 64
	priv, err := GeneratePrivateKey(uint16(n))
	if err != nil {
		t.Errorf("Error NewKeyPair: %v", err)
	}
	pub := priv.GetPublicKey()
	log.Printf("pubkey size: %v", len(pub.h))
	pub.h = []int16{1563, 10333, 9743, 1218, 7437, 1304, 5063, 12105, 976, 6444, 3957, 8542, 1134, 4969, 1830, 6142, 5783, 634, 7169, 10502, 10920, 5798, 7986, 12165, 3839, 10474, 9343, 5701, 11695, 5465, 12123, 6831, 11443, 7050, 6646, 8668, 4189, 8818, 2122, 7685, 10202, 9843, 3290, 6401, 8237, 4683, 2073, 8893, 3730, 5374, 3001, 9924, 7371, 959, 5749, 9207, 2677, 10080, 7638, 1486, 7486, 3329, 956, 8090}

	message := make([][]uint8, 1000)
	for i := 0; i < 1000; i++ {
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

	index = 0
	read_lines := strings.Split(string(s), "\n")
	for _, line := range read_lines {

		r := strings.NewReader(line)
		scanner := bufio.NewScanner(r)
		scanner.Split(bufio.ScanWords)
		var signature []uint8
		for scanner.Scan() {
			x, err := strconv.Atoi(scanner.Text())
			if err != nil {
				t.Error("error converting bytearray to signature")
			}
			signature = append(signature, uint8(x))
		}

		if len(signature) == 0 {
			log.Printf("index: %v\n", index)
			break
		}

		remainder := index % 1000
		var signThis []uint8
		signThis = message[remainder]
		fmt.Println("message: ", message[remainder])

		verification := pub.Verify([]byte(signThis), []byte(signature))
		if verification == false {
			t.Error("Error verifying signature")
		} else {
			log.Printf("Verification OK")
		}
		index++
	}
}
