use std::fmt;

use satoxid::{
    constraints::{AtLeastK, ExactlyK, If, Or},
    Backend, CadicalEncoder, Encoder, Model,
};

// Implementation of Einstein's Puzzle.
// https://web.stanford.edu/~laurik/fsmbook/examples/Einstein'sPuzzle.html

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, strum::EnumIter)]
enum Color {
    Red,
    Yellow,
    Blue,
    Green,
    White,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, strum::EnumIter)]
enum Nationality {
    English,
    Swedish,
    German,
    Danish,
    Norwegian,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, strum::EnumIter)]
enum Drink {
    Tea,
    Coffee,
    Milk,
    Bier,
    Water,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, strum::EnumIter)]
enum Cigarette {
    PallMall,
    Dunhills,
    Blend,
    Prince,
    BlueMasters,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, strum::EnumIter)]
enum Pet {
    Dogs,
    Birds,
    Fish,
    Cats,
    Horses,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, derive_more::From)]
enum Property {
    Color(Color),
    Nationality(Nationality),
    Pet(Pet),
    Cigarette(Cigarette),
    Drink(Drink),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct House {
    number: u32,
    property: Property,
}

fn encode_every_house_has_one_of_each_property<P, B>(encoder: &mut Encoder<House, B>)
where
    P: Into<Property> + strum::IntoEnumIterator,
    <P as strum::IntoEnumIterator>::Iterator: Clone,
    B: Backend,
{
    for house_number in 0..5 {
        let lits = P::iter().map(Into::into).map(|property| House {
            number: house_number,
            property,
        });
        encoder.add_constraint(ExactlyK { k: 1, lits });
    }
}

fn encode_every_property_value_appears_once<P, B>(encoder: &mut Encoder<House, B>)
where
    P: Into<Property> + strum::IntoEnumIterator,
    <P as strum::IntoEnumIterator>::Iterator: Clone,
    B: Backend,
{
    for property in P::iter() {
        let property = property.into();
        let lits = (0..5).map(|number| House { number, property });
        encoder.add_constraint(AtLeastK { k: 1, lits });
    }
}

fn encode_general_rules(encoder: &mut Encoder<House, impl Backend>) {
    // Every house as exactly one of each of the five properties.
    encode_every_house_has_one_of_each_property::<Color, _>(encoder);
    encode_every_house_has_one_of_each_property::<Nationality, _>(encoder);
    encode_every_house_has_one_of_each_property::<Pet, _>(encoder);
    encode_every_house_has_one_of_each_property::<Drink, _>(encoder);
    encode_every_house_has_one_of_each_property::<Cigarette, _>(encoder);

    // Every value of each property only appears once.
    encode_every_property_value_appears_once::<Color, _>(encoder);
    encode_every_property_value_appears_once::<Nationality, _>(encoder);
    encode_every_property_value_appears_once::<Pet, _>(encoder);
    encode_every_property_value_appears_once::<Drink, _>(encoder);
    encode_every_property_value_appears_once::<Cigarette, _>(encoder);
}

fn encode_if_then_constraint(
    encoder: &mut Encoder<House, impl Backend>,
    if_prop: impl Into<Property>,
    then_prop: impl Into<Property>,
) {
    let if_prop = if_prop.into();
    let then_prop = then_prop.into();

    for number in 0..5 {
        encoder.add_constraint(If {
            cond: House {
                number,
                property: if_prop,
            },
            then: House {
                number,
                property: then_prop,
            },
        })
    }
}

fn encode_neighbor_if_then_constraint(
    encoder: &mut Encoder<House, impl Backend>,
    if_prop: impl Into<Property>,
    then_prop: impl Into<Property>,
) {
    let if_prop = if_prop.into();
    let then_prop = then_prop.into();

    for number in 0..5 {
        let neighbors = [-1i32, 1]
            .iter()
            .map(|i| number + i)
            .filter(|&i| 0 <= i && i < 5)
            .map(|neighbor_number| House {
                number: neighbor_number as u32,
                property: then_prop,
            });

        let number = number as u32;

        encoder.add_constraint(If {
            cond: House {
                number,
                property: if_prop,
            },
            then: Or(neighbors),
        });
    }
}

fn encode_specific_rules(encoder: &mut Encoder<House, impl Backend>) {
    // 1. The Englishman lives in the red house.
    encode_if_then_constraint(encoder, Nationality::English, Color::Red);

    // 2. The Swede keeps dogs.
    encode_if_then_constraint(encoder, Nationality::Swedish, Pet::Dogs);

    // 3. The Dane drinks tea.
    encode_if_then_constraint(encoder, Nationality::Danish, Drink::Tea);

    // 4. The green house is just to the left of the white one.
    for number in 0..4 {
        encoder.add_constraint(If {
            cond: House {
                number,
                property: Property::Color(Color::Green),
            },
            then: House {
                number: number + 1,
                property: Property::Color(Color::White),
            },
        });
    }

    // 5. The owner of the green house drinks coffee.
    encode_if_then_constraint(encoder, Color::Green, Drink::Coffee);

    // 6. The Pall Mall smoker keeps birds.
    encode_if_then_constraint(encoder, Cigarette::PallMall, Pet::Birds);

    // 7. The owner of the yellow house smokes Dunhills.
    encode_if_then_constraint(encoder, Color::Yellow, Cigarette::Dunhills);

    // 8. The man in the center house drinks milk.
    encoder.add_constraint(House {
        number: 2,
        property: Property::Drink(Drink::Milk),
    });

    // 9. The Norwegian lives in the first house.
    encoder.add_constraint(House {
        number: 0,
        property: Property::Nationality(Nationality::Norwegian),
    });

    // 10. The Blend smoker has a neighbor who keeps cats.
    encode_neighbor_if_then_constraint(encoder, Cigarette::Blend, Pet::Cats);

    // 11. The man who smokes Blue Masters drinks bier.
    encode_if_then_constraint(encoder, Cigarette::BlueMasters, Drink::Bier);

    // 12. The man who keeps horses lives next to the Dunhill smoker.
    encode_neighbor_if_then_constraint(encoder, Pet::Horses, Cigarette::Dunhills);

    // 13. The German smokes Prince.
    encode_if_then_constraint(encoder, Nationality::German, Cigarette::Prince);

    // 14. The Norwegian lives next to the blue house.
    encode_neighbor_if_then_constraint(encoder, Nationality::Norwegian, Color::Blue);

    // 15. The Blend smoker has a neighbor who drinks water.
    encode_neighbor_if_then_constraint(encoder, Cigarette::Blend, Drink::Water);
}

fn print_property<P>(number: u32, model: &Model<House>)
where
    P: Into<Property> + strum::IntoEnumIterator + fmt::Debug + Copy,
{
    for p in P::iter() {
        let property = p.into();
        if model.var(House { number, property }).unwrap() {
            print!(", {:?}", p);
        }
    }
}

fn main() {
    let mut encoder = CadicalEncoder::new();

    encode_general_rules(&mut encoder);

    encode_specific_rules(&mut encoder);

    if let Some(model) = encoder.solve() {
        for number in 0..5 {
            print!("{}", number);

            print_property::<Color>(number, &model);
            print_property::<Nationality>(number, &model);
            print_property::<Pet>(number, &model);
            print_property::<Drink>(number, &model);
            print_property::<Cigarette>(number, &model);

            println!();
        }

        for number in 0..5 {
            if model
                .var(House {
                    number,
                    property: Property::Pet(Pet::Fish),
                })
                .unwrap()
            {
                println!(
                    "The fish is owned by the person in House number {}.",
                    number
                );
            }
        }
    } else {
        println!("Puzzle is impossible to solve!");
    }
}
