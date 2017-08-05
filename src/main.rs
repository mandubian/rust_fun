use std::marker::PhantomData;


// fake type
#[derive(Clone, Debug)]
enum CNil {}

// coproduct type constrained by IsCop to avoid building bad formatted Cop
#[derive(Clone, Debug)]
enum Cop<L, R> where Cop<L, R>:IsCop {
  Inl(L),
  Inr(R),
}

// Constraint 
trait IsCop {}
impl<L> IsCop for Cop<L, CNil> {}
impl<L, R : IsCop> IsCop for Cop<L, R> {}


#[derive(Clone, Debug)]
struct CNilK<A> {
  _m: PhantomData<A>
}

#[derive(Clone, Debug)]
enum CopK<A, L, R> where CopK<A, L, R>:IsCopK {
  Inl(L, PhantomData<A>),
  Inr(R, PhantomData<A>),
}


// a Kinded type (F: * -> *)
trait IsKinded<A> {}
impl<A> IsKinded<A> for Vec<A> {}
impl<A> IsKinded<A> for Option<A> {}
impl<A> IsKinded<A> for CNilK<A> {}
impl<A, L: IsKinded<A>> IsKinded<A> for CopK<A, L, CNilK<A>> {}
impl<A, L: IsKinded<A>, R : IsCopK + IsKinded<A>> IsKinded<A> for CopK<A, L, R> {}

trait IsCopK {}
impl<A, L: IsKinded<A>> IsCopK for CopK<A, L, CNilK<A>> {}
impl<A, L: IsKinded<A>, R : IsCopK + IsKinded<A>> IsCopK for CopK<A, L, R> {}

// a Kinded type (F: * -> *) structure which can build a type F[B] from a F[A]
trait Kinded<B> {
  type A;  // A
  type FB : IsKinded<B> ; // F[B]
}

// macro helper
macro_rules! derive_kinded {
  ($t:ident) => {
    impl<T, U> Kinded<U> for $t<T> {
      type A = T;
      type FB = $t<U>;
    }
  }
}

derive_kinded!(Vec);
derive_kinded!(Option);

// CopK Kinded<B>
impl<A, B, L: IsKinded<A> + Kinded<A> + Kinded<B>> Kinded<B> for CopK<A, L, CNilK<A>>
  where <L as Kinded<B>>::FB : Kinded<B> {
  type A = A;
  type FB = CopK<B, <L as Kinded<B>>::FB, CNilK<B>>;
}

impl<A, B, L: IsKinded<A> + Kinded<A> + Kinded<B>, R: IsCopK + IsKinded<A> + Kinded<A> + Kinded<B>> Kinded<B> for CopK<A, L, R>
  where <L as Kinded<B>>::FB : Kinded<B>, <R as Kinded<B>>::FB: IsCopK {
  type A = A;
  type FB = CopK<B, <L as Kinded<B>>::FB, <R as Kinded<B>>::FB>;
}

impl<A, B> Kinded<B> for CNilK<A> {
  type A = A;
  type FB = CNilK<B>;
}


// Functor
trait Functor<A, B> where Self:Kinded<B> {
  fn map<F>(&self, f:F) -> <Self as Kinded<B>>::FB where F: Fn(&A) -> B;
}

impl<A, B> Functor<A, B> for Option<A> {
  fn map<F>(&self, f:F) -> <Self as Kinded<B>>::FB where F: Fn(&A) -> B {
    match self {
      &Some(ref a) => Some(f(a)),
      &None => None
    }
  }
} 

impl<A, B> Functor<A, B> for Vec<A> {
  fn map<F>(&self, f:F) -> <Self as Kinded<B>>::FB where F: Fn(&A) -> B {        
    let mut v = Vec::<B>::new();
    for x in self {
      v.push(f(x));
    }
    v
  }
} 

impl<
  A, B,
  L: IsKinded<A> + Kinded<A> + Functor<A, B>
> Functor<A, B> for CopK<A, L, CNilK<A>>
  where <L as Kinded<B>>::FB : Kinded<B> {
  fn map<F>(&self, f:F) -> <Self as Kinded<B>>::FB where F: Fn(&A) -> B {        
    match self {
      &CopK::Inl(ref l, _) => CopK::Inl(l.map(f), PhantomData),
      &CopK::Inr(_, _) => panic!("can't reach that case"),
    }
  }
} 


impl<
  A, B,
  L: IsKinded<A> + Kinded<A> + Functor<A, B>,
  R: IsCopK + IsKinded<A> + Kinded<A> + Functor<A, B>
> Functor<A, B> for CopK<A, L, R>
  where <L as Kinded<B>>::FB : Kinded<B>, <R as Kinded<B>>::FB: IsCopK {
  fn map<F>(&self, f:F) -> <Self as Kinded<B>>::FB where F: Fn(&A) -> B {        
    match self {
      &CopK::Inl(ref l, _) => CopK::Inl(l.map(f), PhantomData),
      &CopK::Inr(ref r, _) => CopK::Inr(r.map(f), PhantomData)
    }
  }
} 


fn main() {
  println!("Hello, world!");

  // let c: Inl<&str, CNil> = Inl::new("toto");
  // let c2: Inr<&str, CNil> = Inr::new("toto");
  // let c: Cop<&u32, Cop<&str, Cop<&u32, CNil>>> = Cop { inr : Cop { inl: "toto" } };
  let c: Cop<u32, Cop<&str, Cop<u32, CNil>>> = Cop::Inr(Cop::Inl("toto"));
  println!("c:{:?}", c);

  let c2: Cop<u32, Cop<&str, CNil>> = Cop::Inr(Cop::Inl("toto"));
  println!("c2:{:?}", c2);

  // type CK = CopK!(&str, Vec, Option);

  let ck: CopK<&str, Vec<&str>, CopK<&str, Option<&str>, CNilK<&str>>> = CopK::Inl(vec!("toto"), PhantomData);
  let ck2: CopK<&str, Vec<&str>, CopK<&str, Option<&str>, CNilK<&str>>> = CopK::Inr(CopK::Inl(Some("toto"), PhantomData), PhantomData);

  let ck_1 = ck.map(|x| format!("{}_{}", x, "tata1"));
  let ck2_1 = ck2.map(|x| format!("{}_{}", x, "tata2"));

  println!("ck:{:?} ck2:{:?} ck_1:{:?} ck2_1:{:?}", ck, ck2, ck_1, ck2_1);

}




// #[macro_export]
// macro_rules! CopK {
//   ($single: ty) => {
//     CopK<$single, CNilK<$single>>
//   };
//   ($simple:ty, $first: ty, $( $repeated: ty ), +) => {
//     CopK<$simple, $first<$single>, CopK!($simple, $($repeated), *)>
//   };
// }

// macro_rules! derive_Kinded {
//     ($t:ident) => {
//         impl<T, U> Kinded<U> for $t<T> {
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

//   fn subst<FA>(f: &FA) -> &<FA as Kinded<B>>::FB where FA : Kinded<B, A = A>;

//   fn coerce(a: &A) -> &B where A: Kinded<B, A = A, FB = B> {
//     Self::subst::<A>(a)
//   }

//   fn prf() -> IsPrf<A, B> { IsPrf::new() }
// }

// impl<A> Is<A, A> for A {
//   fn subst<FA>(f: &FA) -> &<FA as Kinded<A>>::FB where FA : Kinded<A, A = A> {
//     unsafe { std::mem::transmute::<&FA, &<FA as Kinded<A>>::FB>(f) }
//   }
// }

// trait IsF<A, B> where Self : Kinded<B, A = A> {
//   fn subst(&self) -> &<Self as Kinded<B>>::FB;
// }

// impl<A, FA> IsF<A, A> for FA where FA : Kinded<A, A = A> {
//   fn subst(&self) -> &<FA as Kinded<A>>::FB {
//     unsafe { std::mem::transmute::<&FA, &<FA as Kinded<A>>::FB>(self) }
//   }
// }


// // <i32 as Is<i32, i32>>::subst(&vec!(1, 2, 3));
// // <String as Is<String, String>>::subst(&vec!("toto".to_string(), "tata".to_string(), "tutu".to_string()));
// println!("{:?}", vec!(1, 2, 3).subst());