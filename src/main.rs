use halo2_proofs::circuit::{AssignedCell, Chip, Layouter, SimpleFloorPlanner};
use halo2_proofs::dev::MockProver;
use halo2_proofs::pasta::{EqAffine, Fp};
use halo2_proofs::plonk::{Advice, Circuit, Column, ConstraintSystem, create_proof, Error, Fixed, Instance, keygen_pk, keygen_vk, Selector};
use halo2_proofs::poly::commitment::Params;
use halo2_proofs::poly::Rotation;
use halo2_proofs::transcript::{Blake2bWrite, Challenge255};
use rand::rngs::OsRng;

trait Ops {
    type Num;
    fn load_private(&self, layouter: impl Layouter<Fp>, x: Option<Fp>) -> Result<Self::Num, Error>;
    fn load_constant(&self, layouter: impl Layouter<Fp>, x: Fp) -> Result<Self::Num, Error>;

    fn mul(
        &self,
        layouter: impl Layouter<Fp>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error>;
    fn add(
        &self,
        layouter: impl Layouter<Fp>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error>;
    fn expose_public(
        &self,
        layouter: impl Layouter<Fp>,
        num: Self::Num,
        row: usize,
    ) -> Result<(), Error>;
}

struct MyChip {
    config: MyConfig,
}

impl MyChip {
    fn new(config: MyConfig) -> Self {
        MyChip { config }
    }

    fn configure(
        meta: &mut ConstraintSystem<Fp>,
        advice: [Column<Advice>; 2],
        instance: Column<Instance>,
        constant: Column<Fixed>,
    ) -> MyConfig {
        meta.enable_constant(constant);
        meta.enable_equality(instance);
        for adv in advice.iter() {
            meta.enable_equality(*adv);
        }
        let s_mul = meta.selector();
        let s_add = meta.selector();

        meta.create_gate("mul/add", |meta| {
            let lhs = meta.query_advice(advice[0], Rotation::cur());
            let rhs = meta.query_advice(advice[1], Rotation::cur());
            let out = meta.query_advice(advice[0], Rotation::next());
            let s_mul = meta.query_selector(s_mul);
            let s_add = meta.query_selector(s_add);

            vec![
                s_mul * (lhs.clone() * rhs.clone() - out.clone()),
                s_add * (lhs + rhs - out),
            ]
        });

        MyConfig {
            advice,
            instance,
            s_mul,
            s_add,
        }
    }
}

impl Chip<Fp> for MyChip {
    type Config = MyConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl Ops for MyChip {
    type Num = AssignedCell<Fp, Fp>;

    fn load_private(
        &self,
        mut layouter: impl Layouter<Fp>,
        v: Option<Fp>,
    ) -> Result<Self::Num, Error> {
        let config = self.config();
        layouter.assign_region(
            || "load_private",
            |mut region| {
                region.assign_advice(
                    || "private value",
                    config.advice[0],
                    0,
                    || v.ok_or(Error::Synthesis),
                )
            },
        )
    }

    fn load_constant(&self, mut layouter: impl Layouter<Fp>, c: Fp) -> Result<Self::Num, Error> {
        let config = self.config();
        layouter.assign_region(
            || "load_constant",
            |mut region| region.assign_advice_from_constant(|| "constant", config.advice[0], 0, c),
        )
    }

    fn mul(
        &self,
        mut layouter: impl Layouter<Fp>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config();
        layouter.assign_region(
            || "mul",
            |mut region| {
                config.s_mul.enable(&mut region, 0)?;
                a.copy_advice(|| "lhs", &mut region, config.advice[0], 0)?;
                b.copy_advice(|| "rhs", &mut region, config.advice[1], 0)?;
                let v = a.value().and_then(|a| b.value().map(|b| *a * *b));
                region.assign_advice(|| "a*b", config.advice[0], 1, || v.ok_or(Error::Synthesis))
            },
        )
    }

    fn add(
        &self,
        mut layouter: impl Layouter<Fp>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config();
        layouter.assign_region(
            || "add",
            |mut region| {
                config.s_add.enable(&mut region, 0)?;
                a.copy_advice(|| "lhs", &mut region, config.advice[0], 0)?;
                b.copy_advice(|| "rhs", &mut region, config.advice[1], 0)?;
                let v = a.value().and_then(|a| b.value().map(|b| *a + *b));
                region.assign_advice(|| "a+b", config.advice[0], 1, || v.ok_or(Error::Synthesis))
            },
        )
    }

    fn expose_public(
        &self,
        mut layouter: impl Layouter<Fp>,
        num: Self::Num,
        row: usize,
    ) -> Result<(), Error> {
        let config = self.config();
        layouter.constrain_instance(num.cell(), config.instance, row)
    }
}

#[derive(Clone, Debug)]
struct MyConfig {
    advice: [Column<Advice>; 2],
    instance: Column<Instance>,
    s_mul: Selector,
    s_add: Selector,
}

#[derive(Default)]
struct MyCircuit {
    constant: Fp,
    x: Option<Fp>, // This is option because when we verify the circuit we will not pass the x
}

impl Circuit<Fp> for MyCircuit {
    type Config = MyConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        return Self::default();
    }

    fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
        let advice = [meta.advice_column(), meta.advice_column()];
        let instance = meta.instance_column();
        let constant = meta.fixed_column();

        MyChip::configure(meta, advice, instance, constant)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fp>,
    ) -> Result<(), Error> {
        let chip = MyChip::new(config);
        let x = chip.load_private(layouter.namespace(|| "load x"), self.x)?;
        let constant = chip.load_constant(layouter.namespace(|| "constant"), self.constant)?;

        let x2 = chip.mul(layouter.namespace(|| "x2"), x.clone(), x.clone())?;
        let x3 = chip.mul(layouter.namespace(|| "x3"), x2, x.clone())?;
        let x3_x = chip.add(layouter.namespace(|| "x3_5"), x3, x)?;
        let x3_x_5 = chip.add(layouter.namespace(|| "x3+x+5"), x3_x, constant)?;

        chip.expose_public(layouter.namespace(|| "expose c"), x3_x_5, 0)
    }
}

fn main() {
    let x = Fp::from(3);
    let constant = Fp::from(5);
    let res = Fp::from(35);

    let circuit = MyCircuit {
        constant,
        x: Some(x), // Pass the x when creating the proof but not on verify
    };

    let public_inputs = vec![res];

    // MOCK PROOVER
    // let prover = MockProver::run(4, &circuit, vec![public_inputs]).unwrap();
    // assert_eq!(prover.verify(), Ok(()));

    // PROOF/VERIFICATION
    // let params: Params<EqAffine> = Params::new(4);
    // let vk = keygen_vk(&params, &circuit).unwrap();
    // let pk = keygen_pk(&params, vk, &circuit).unwrap();
    //
    // let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    //
    // let proof = create_proof(
    //     &params,
    //     &pk,
    //     &[circuit.clone()],
    //     &[&[&[res]]],
    //     OsRng,
    //     &mut transcript,
    // );
    //

    // PLOTTING SECTION
    use plotters::prelude::*;
    let root = BitMapBackend::new("layout.png", (1024, 768)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root
        .titled("Example Circuit Layout", ("sans-serif", 60))
        .unwrap();

    halo2_proofs::dev::CircuitLayout::default()
        // You can optionally render only a section of the circuit.
        .view_width(0..7)
        .view_height(0..60)
        // You can hide labels, which can be useful with smaller areas.
        .show_labels(true)
        // Render the circuit onto your area!
        // The first argument is the size parameter for the circuit.
        .render(5, &circuit, &root)
        .unwrap();

    let dot_string = halo2_proofs::dev::circuit_dot_graph(&circuit);

    // Now you can either handle it in Rust, or just
    // print it out to use with command-line tools.
    print!("{}", dot_string);
}
