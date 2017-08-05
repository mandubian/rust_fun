use std::marker::PhantomData;

// Having fun in Rust trying to mimic higher-kind structures, abstracting on type constructors
// Inspired by different existing rust projects:
// - https://github.com/Sgeo/hlist/blob/master/src/lib.rs
// - https://github.com/lloydmeta/frunk/blob/master/src/functor.rs

// Basic Coproduct (like scala shapeless coproduct L :+: R)

// non-instantiable type to represent coproduct ending type CNil
#[derive(Clone, Debug)]
enum CNil {}

// coproduct type constrained by IsCop to avoid building bad Cop
#[derive(Clone, Debug)]
enum Cop<L, R> where Cop<L, R>:IsCop {
  Inl(L),
  Inr(R),
}

// Constraint
// - L :+: CNil is a Coproduct but CNil can't exist
// - L :+: R requires R to a Coproduct
trait IsCop {}
impl<L> IsCop for Cop<L, CNil> {}
impl<L, R : IsCop> IsCop for Cop<L, R> {}


// Coproduct of type constructors
// Cop<A> = Vec<A> :+: Option<A> :+: CNilK<A>

// Couldn't make it non-instantiable type
#[derive(Clone, Debug)]
struct CNilK<A> {
  _m: PhantomData<A>
}

// The Type-Constructor Coproduct Cop<A> = Left<A> :+: Right<A> constrained by IsCopK so that
// I would have liked to use new Rust unions here but was blocked by unsafe union pattern matching that behaved weird
#[derive(Clone, Debug)]
enum CopK<A, L, R> where CopK<A, L, R>:IsCopK {
  // we need PhantomData to keep track of type A
  Inl(L, PhantomData<A>),
  Inr(R, PhantomData<A>),
}

// Macro CopK type helper
macro_rules! CopK {
  ($simple:ty, $first: ty) => {
    CopK<$simple, $first, CNilK<$simple>>
  };
  ($simple:ty, $first: ty, $( $repeated: ty ), +) => {
    CopK<$simple, $first, CopK!($simple, $($repeated), *)>
  };
}


// Simple type constructor notice (F: * -> *)
trait IsTypeCons<A> {}
impl<A> IsTypeCons<A> for Vec<A> {}
impl<A> IsTypeCons<A> for Option<A> {}
impl<A> IsTypeCons<A> for CNilK<A> {}
impl<A, L: IsTypeCons<A>> IsTypeCons<A> for CopK<A, L, CNilK<A>> {}
impl<A, L: IsTypeCons<A>, R : IsCopK + IsTypeCons<A>> IsTypeCons<A> for CopK<A, L, R> {}


// Constraint
// - L<A> :+: CNilK<A> is a Coproduct but CNil<A> can't exist
// - L<A> :+: R<A> requires R<AQ to a Coproduct
trait IsCopK {}
impl<A, L: IsTypeCons<A>> IsCopK for CopK<A, L, CNilK<A>> {}
impl<A, L: IsTypeCons<A>, R : IsCopK + IsTypeCons<A>> IsCopK for CopK<A, L, R> {}

// The Type Constructor (F: * -> *) which can build a type F[B] from a F[A]
// In theory, IsTypeCons could be proven from TypeCons but rust compiler wasn't happy about that... need deeper studying
trait TypeCons<B> {
  type A;  // A
  type FB : IsTypeCons<B> ; // F[B]
}

// TypeCons macro helper
macro_rules! derive_TypeCons {
  ($t:ident) => {
    impl<T, U> TypeCons<U> for $t<T> {
      type A = T;
      type FB = $t<U>;
    }
  }
}

derive_TypeCons!(Vec);
derive_TypeCons!(Option);

// CopK TypeCons<B>
impl<A, B, L: IsTypeCons<A> + TypeCons<A> + TypeCons<B>> TypeCons<B> for CopK<A, L, CNilK<A>>
  where <L as TypeCons<B>>::FB : TypeCons<B> {
  type A = A;
  type FB = CopK<B, <L as TypeCons<B>>::FB, CNilK<B>>;
}

impl<A, B, L: IsTypeCons<A> + TypeCons<A> + TypeCons<B>, R: IsCopK + IsTypeCons<A> + TypeCons<A> + TypeCons<B>> TypeCons<B>
  for CopK<A, L, R>
  where <L as TypeCons<B>>::FB : TypeCons<B>, <R as TypeCons<B>>::FB: IsCopK {
    type A = A;
    type FB = CopK<B, <L as TypeCons<B>>::FB, <R as TypeCons<B>>::FB>;
  }

impl<A, B> TypeCons<B> for CNilK<A> {
  type A = A;
  type FB = CNilK<B>;
}


// Functor
// A & B are required to identify morphism (A -> B) and build TypeCons<B>
trait Functor<A, B> where Self:TypeCons<B> {
  fn map<F>(&self, f:F) -> <Self as TypeCons<B>>::FB where F: Fn(&A) -> B;
}

// Functor for Option
impl<A, B> Functor<A, B> for Option<A> {
  fn map<F>(&self, f:F) -> <Self as TypeCons<B>>::FB where F: Fn(&A) -> B {
    match self {
      &Some(ref a) => Some(f(a)),
      &None => None
    }
  }
} 

// Functor for Vec
impl<A, B> Functor<A, B> for Vec<A> {
  fn map<F>(&self, f:F) -> <Self as TypeCons<B>>::FB where F: Fn(&A) -> B {        
    let mut v = Vec::<B>::new();
    for x in self {
      v.push(f(x));
    }
    v
  }
} 

// Functor for CopK
impl<A, B, L: IsTypeCons<A> + TypeCons<A> + Functor<A, B>>
  Functor<A, B> for CopK<A, L, CNilK<A>>
  where <L as TypeCons<B>>::FB : TypeCons<B> {
    fn map<F>(&self, f:F) -> <Self as TypeCons<B>>::FB where F: Fn(&A) -> B {        
      match self {
        &CopK::Inl(ref l, _) => CopK::Inl(l.map(f), PhantomData),
        &CopK::Inr(_, _) => panic!("can't reach that case"),
      }
    }
  }

impl<
  A, B,
  L: IsTypeCons<A> + TypeCons<A> + Functor<A, B>,
  R: IsCopK + IsTypeCons<A> + TypeCons<A> + Functor<A, B>
> Functor<A, B> for CopK<A, L, R>
  where <L as TypeCons<B>>::FB : TypeCons<B>, <R as TypeCons<B>>::FB: IsCopK {
    fn map<F>(&self, f:F) -> <Self as TypeCons<B>>::FB where F: Fn(&A) -> B {        
      match self {
        &CopK::Inl(ref l, _) => CopK::Inl(l.map(f), PhantomData),
        &CopK::Inr(ref r, _) => CopK::Inr(r.map(f), PhantomData)
      }
    }
  }


fn main() {

  // Basic Coproduct
  let c: Cop<u32, Cop<&str, Cop<u32, CNil>>> = Cop::Inr(Cop::Inl("toto"));
  println!("c:{:?}", c);

  let c2: Cop<u32, Cop<&str, CNil>> = Cop::Inr(Cop::Inl("toto"));
  println!("c2:{:?}", c2);

  // Type-Constructor Coproduct
  let ck: CopK!(&str, Vec<&str>, Option<&str>) = CopK::Inl(vec!("toto"), PhantomData);
  let ck2: CopK!(&str, Vec<&str>, Option<&str>) = CopK::Inr(CopK::Inl(Some("toto"), PhantomData), PhantomData);

  let ck_1 = ck.map(|x| format!("{}_{}", x, "tata1"));
  let ck2_1 = ck2.map(|x| format!("{}_{}", x, "tata2"));

  println!("ck:{:?} ck2:{:?} ck_1:{:?} ck2_1:{:?}", ck, ck2, ck_1, ck2_1);

  let ckk: CopK!(i32, Vec<i32>, Option<i32>) = CopK::Inl(vec!(42), PhantomData);
  let ckk2: CopK!(i32, Vec<i32>, Option<i32>) = CopK::Inr(CopK::Inl(Some(42), PhantomData), PhantomData);

  // Using Functor of CopK
  let ckk_1 = ckk.map(|x| x + 1);
  let ckk2_1 = ckk2.map(|x| x + 1);

  println!("ckk:{:?} ckk2:{:?} ckk_1:{:?} ckk2_1:{:?}", ckk, ckk2, ckk_1, ckk2_1);

}














// keeping track of experiments


// macro_rules! derive_TypeCons {
//     ($t:ident) => {
//         impl<T, U> TypeCons<U> for $t<T> {
//             type C = T;
//             type T = $t<U>;
//         }
//     }
// }



// #[derive(Clone, Debug)]
// struct Inl<L, R> {
//   l: L,
//   _marker: PhantomData<R>
// }

// impl<L, R> Inl<L, R> {
//   fn new(l: L) -> Inl<L, R> {
//     Inl {
//       l: l,
//       _marker : PhantomData
//     }
//   }
// }

// #[derive(Clone, Debug)]
// struct Inr<L, R> {
//   r: R,
//   _marker: PhantomData<L>
// }

// impl<L, R> Inr<L, R> {
//   fn new(r: R) -> Inr<L, R> {
//     Inr {
//       r: r,
//       _marker : PhantomData
//     }
//   }
// }

// trait C {
//   type T;
//   fn value(&self) -> &Self::T;
// }

// impl<L> C for Inl<L, CNil> {
//   type T = L;
//   fn value(&self) -> &L { &self.l }
// }

// impl<L, R> C for Inl<L, R> where R : IsCop {
//   type T = L;
//   fn value(&self) -> &L { &self.l }
// }

// impl<L, R> C for Inr<L, R> where R : C {
//   type T = <R as C>::T;
//   fn value(&self) -> &<R as C>::T { &self.r.value() }
// }


// trait IsPrfPhantom<A, B> {}

// struct IsPrf<A, B> {
//   phantom: PhantomData<IsPrfPhantom<A, B>>,
// }

// impl<A, B> IsPrf<A, B> {
//   fn new() -> IsPrf<A, B> {
//     IsPrf { phantom: PhantomData }
//   }
// }

// trait Is<A, B> {

//   fn subst<FA>(f: &FA) -> &<FA as TypeCons<B>>::FB where FA : TypeCons<B, A = A>;

//   fn coerce(a: &A) -> &B where A: TypeCons<B, A = A, FB = B> {
//     Self::subst::<A>(a)
//   }

//   fn prf() -> IsPrf<A, B> { IsPrf::new() }
// }

// impl<A> Is<A, A> for A {
//   fn subst<FA>(f: &FA) -> &<FA as TypeCons<A>>::FB where FA : TypeCons<A, A = A> {
//     unsafe { std::mem::transmute::<&FA, &<FA as TypeCons<A>>::FB>(f) }
//   }
// }

// trait IsF<A, B> where Self : TypeCons<B, A = A> {
//   fn subst(&self) -> &<Self as TypeCons<B>>::FB;
// }

// impl<A, FA> IsF<A, A> for FA where FA : TypeCons<A, A = A> {
//   fn subst(&self) -> &<FA as TypeCons<A>>::FB {
//     unsafe { std::mem::transmute::<&FA, &<FA as TypeCons<A>>::FB>(self) }
//   }
// }


// // <i32 as Is<i32, i32>>::subst(&vec!(1, 2, 3));
// // <String as Is<String, String>>::subst(&vec!("toto".to_string(), "tata".to_string(), "tutu".to_string()));
// println!("{:?}", vec!(1, 2, 3).subst());