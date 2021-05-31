package main_test

import (
	"sync"
	"testing"
	"time"

	"github.com/google/go-cmp/cmp"
	"github.com/google/go-cmp/cmp/cmpopts"
)

type Person struct {
	ID   int
	Name string
	Age  int
}

func TestIgnoreFields(t *testing.T) {
	john := Person{
		ID:   1,
		Name: "john",
		Age:  20,
	}
	anotherJohn := Person{
		ID:   2,
		Name: "john",
		Age:  20,
	}

	// Ignore fields when comparing two structs.
	opts := cmpopts.IgnoreFields(Person{}, "ID")
	if !cmp.Equal(john, anotherJohn, opts) {
		t.Errorf("expected %v to equal %v", john, anotherJohn)
	}
	// Print out the log if the opts is not  provided.
	t.Log(cmp.Diff(john, anotherJohn))
}

func TestIgnoreNestedFields(t *testing.T) {
	type Bar struct {
		Name string
	}
	type Foo struct {
		Name string
		Bar  Bar
	}
	foo := Foo{
		Name: "foo",
		Bar: Bar{
			Name: "bar",
		},
	}
	anotherFoo := Foo{
		Name: "foo",
		Bar: Bar{
			Name: "not-bar",
		},
	}

	// Ignore fields when comparing two structs.
	opts := cmpopts.IgnoreFields(Foo{}, "Bar.Name")
	if diff := cmp.Diff(foo, anotherFoo, opts); diff != "" {
		t.Errorf("nested fields mismatch (-want +got):\n%s", diff)
	} else {
		// Log diff if the opts is not  provided.
		t.Log(cmp.Diff(foo, anotherFoo))
	}
}

func TestEqualApproxMargin(t *testing.T) {
	tests := []struct {
		scenario string
		a, b     float64
		approx   bool
	}{
		{"99.9 == 100.0?", 99.9, 100.0, true},
		{"100.0 == 100.0?", 100.0, 100.0, true},
		{"100.1 == 100.0?", 100.1, 100.0, true},
		{"100.2 == 100.0?", 100.2, 100.0, false},
		{"200.0 == 100.0", 200.0, 100.0, false},
	}
	// Allow a difference of up to 1 decimal place.
	opts := cmpopts.EquateApprox(0, 0.1)
	for _, tt := range tests {
		t.Run(tt.scenario, func(t *testing.T) {
			if tt.approx != cmp.Equal(tt.a, tt.b, opts) {
				diff := cmp.Diff(tt.a, tt.b, opts)
				t.Errorf("a = b mismatch (-want +got):\n%s", diff)
			}
		})
	}
}

func TestEquatApproxFraction(t *testing.T) {
	tests := []struct {
		scenario string
		a, b     float64
		approx   bool
	}{
		{"49.9 == 100.0?", 49.9, 100.0, false},
		{"50.0 == 100.0?", 50.0, 100.0, true},
		{"75.0 == 100.0?", 75.0, 100.0, true},
		{"99.9 == 100.0?", 99.9, 100.0, true},
		{"100.0 == 100.0?", 100.0, 100.0, true},
		{"100.1 == 100.0?", 100.1, 100.0, true},
		{"100.2 == 100.0?", 100.2, 100.0, true},
		{"200.0 == 100.0", 200.0, 100.0, true},
		{"300.0 == 100.0", 300.0, 100.0, false},
		{"500.0 == 100.0", 500.0, 100.0, false},
		{"1000.0 == 100.0", 1000.0, 100.0, false},
	}
	// How does this approximate fraction works?
	//
	// |x-y| ≤ max(fraction*min(|x|, |y|), margin)
	//
	// Find the min of the two values, n
	// multiply it with the fraction, f
	// Take the max of the f*n and the margin, o
	// The delta of the two values must be less or equal o.
	atLeastHalf := cmpopts.EquateApprox(1.0, 0)
	for _, tt := range tests {
		t.Run(tt.scenario, func(t *testing.T) {
			if tt.approx != cmp.Equal(tt.a, tt.b, atLeastHalf) {
				diff := cmp.Diff(tt.a, tt.b, atLeastHalf)
				t.Errorf("a = b mismatch (-want +got):\n%s", diff)
			}
		})
	}

	t.Run("delta one", func(t *testing.T) {
		// |x-y| ≤ max(fraction*min(|x|, |y|), margin)
		oneOfHundreth := cmpopts.EquateApprox(0.01, 0)
		if diff := cmp.Diff(100.0, 101.0, oneOfHundreth); diff != "" {
			t.Errorf("100.0 == 101.0 mismatch (-want +got):\n%s", diff)
		}
	})
}

func TestEquateApproxTime(t *testing.T) {
	now := time.Now()

	// Allows difference of up to 10 seconds.
	opts := cmpopts.EquateApproxTime(10 * time.Second)

	tests := []struct {
		scenario string
		t0, t1   time.Time
		approx   bool
	}{
		{"delta 0 seconds", now, now, true},
		{"delta 5 seconds", now, now.Add(5 * time.Second), true},
		{"delta 10 seconds", now, now.Add(10 * time.Second), true},
		{"delta 11 seconds", now, now.Add(11 * time.Second), false},
		{"delta 20 seconds", now, now.Add(20 * time.Second), false},
	}

	for _, tt := range tests {
		t.Run(tt.scenario, func(t *testing.T) {
			if tt.approx != cmp.Equal(tt.t0, tt.t1, opts) {
				diff := cmp.Diff(tt.t0, tt.t1, opts)
				t.Errorf("time mismatch (-want +got):\n%s", diff)
			}
		})
	}
}

func TestEquateEmpty(t *testing.T) {
	// Allows slices and maps to be equal, regardless of whether they are nil.
	opts := cmpopts.EquateEmpty()

	var m map[string]interface{}
	var n []int

	tests := []struct {
		scenario string
		a, b     interface{}
		eq       bool
	}{
		{"empty person", new(Person), &Person{}, true},
		{"person with fields", &Person{Name: "John"}, nil, false},
		{"empty maps", make(map[string]interface{}, 0), m, true},
		{"empty slice", make([]int, 0), n, true},
	}

	for _, tt := range tests {
		t.Run(tt.scenario, func(t *testing.T) {
			if tt.eq != cmp.Equal(tt.a, tt.b, opts) {
				diff := cmp.Diff(tt.a, tt.b, opts)
				t.Errorf("types mismatch (-want +got):\n%s", diff)
			}
		})
	}
}

func TestSliceOrder(t *testing.T) {
	t.Run("sorted int", func(t *testing.T) {
		opts := cmpopts.SortSlices(func(a, b int) bool {
			return a < b
		})
		a := []int{1, 2, 3}
		b := []int{3, 2, 1}
		if diff := cmp.Diff(a, b, opts); diff != "" {
			t.Errorf("sort mismatch (-want +got):\n%s", diff)
		}
	})

	t.Run("sorted string", func(t *testing.T) {
		opts := cmpopts.SortSlices(func(a, b string) bool {
			return a < b
		})
		a := []string{"foo", "bar"}
		b := []string{"bar", "foo"}
		if diff := cmp.Diff(a, b, opts); diff != "" {
			t.Errorf("sort mismatch (-want +got):\n%s", diff)
		}
	})

	t.Run("sorted struct", func(t *testing.T) {
		opts := cmpopts.SortSlices(func(a, b Person) bool {
			return a.Age < b.Age
		})
		a := []Person{{Age: 10}, {Age: 20}}
		b := []Person{{Age: 20}, {Age: 10}}
		if diff := cmp.Diff(a, b, opts); diff != "" {
			t.Errorf("sort mismatch (-want +got):\n%s", diff)
		}
	})

	t.Run("sorted maps - int keys", func(t *testing.T) {
		opts := cmpopts.SortMaps(func(a, b int) bool {
			return a < b
		})
		a := map[int]string{0: "zero", 1: "one"}
		b := map[int]string{1: "one", 0: "zero"}
		if diff := cmp.Diff(a, b, opts); diff != "" {
			t.Errorf("sort mismatch (-want +got):\n%s", diff)
		}
	})

	t.Run("sorted maps - str keys", func(t *testing.T) {
		opts := cmpopts.SortMaps(func(a, b int) bool {
			return a < b
		})
		a := map[string]int{"zero": 0, "one": 1}
		b := map[string]int{"one": 1, "zero": 0}
		if diff := cmp.Diff(a, b, opts); diff != "" {
			t.Errorf("sort mismatch (-want +got):\n%s", diff)
		}
	})
}

func TestIgnore(t *testing.T) {
	t.Run("ignore types", func(t *testing.T) {
		type Lock struct {
			Once sync.Once
			Name string
		}

		opts := cmpopts.IgnoreTypes(sync.Once{})
		a := &Lock{Name: "1"}
		b := &Lock{Name: "1"}
		if diff := cmp.Diff(a, b, opts); diff != "" {
			t.Errorf("sort mismatch (-want +got):\n%s", diff)
		}
	})

	t.Run("ignore map entries", func(t *testing.T) {
		opts := cmpopts.IgnoreMapEntries(func(k string, v interface{}) bool {
			// Ignore if the key is id.
			return k == "id"
		})
		a := map[string]interface{}{"id": 1, "name": "john"}
		b := map[string]interface{}{"id": 2, "name": "john"}
		if diff := cmp.Diff(a, b, opts); diff != "" {
			t.Errorf("sort mismatch (-want +got):\n%s", diff)
		}
	})

	t.Run("ignore slice entries", func(t *testing.T) {
		// Filter out non-johns.
		opts := cmpopts.IgnoreSliceElements(func(person Person) bool {
			return person.Name != "john"
		})
		a := []Person{{Name: "john"}, {Name: "jane"}, {Name: "alice"}}
		b := []Person{{Name: "jane"}, {Name: "alice"}, {Name: "john"}}
		if diff := cmp.Diff(a, b, opts); diff != "" {
			t.Errorf("sort mismatch (-want +got):\n%s", diff)
		}
	})

	t.Run("ignore slice entries", func(t *testing.T) {
		type Credentials struct {
			Email    string
			password string
		}
		a := Credentials{Email: "john.doe@mail.com", password: "zxc#v023r"}
		b := Credentials{Email: "john.doe@mail.com", password: "saf908234"}

		opts := cmpopts.IgnoreUnexported(Credentials{})
		if diff := cmp.Diff(a, b, opts); diff != "" {
			t.Errorf("sort mismatch (-want +got):\n%s", diff)
		}
	})
}
