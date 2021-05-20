use sat_encoder::{
    constraints::{AtLeastK, ExactlyK, If, Or},
    Backend, CadicalEncoder, Encoder,
    Lit::Pos,
};
use strum::IntoEnumIterator;

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

macro_rules! every_house_has_one_of_each_property {
    ($prop:ident, $encoder:expr) => {
        for house_number in 0..5 {
            let lits = $prop::iter()
                .map(Property::$prop)
                .map(|property| House {
                    number: house_number,
                    property,
                })
                .map(Pos);
            $encoder.add_constraint(ExactlyK { k: 1, lits });
        }
    };
}

macro_rules! every_property_value_appears_once {
    ($prop:ident, $encoder:expr) => {
        for p in $prop::iter() {
            let lits = (0..5)
                .map(|number| House {
                    number,
                    property: Property::$prop(p),
                })
                .map(Pos);
            $encoder.add_constraint(AtLeastK { k: 1, lits });
        }
    };
}

fn encode_general_rules(encoder: &mut Encoder<House, impl Backend>) {
    // Every house as exactly one of each of the five properties.
    every_house_has_one_of_each_property!(Color, encoder);
    every_house_has_one_of_each_property!(Nationality, encoder);
    every_house_has_one_of_each_property!(Pet, encoder);
    every_house_has_one_of_each_property!(Drink, encoder);
    every_house_has_one_of_each_property!(Cigarette, encoder);

    // Every value of each property only appears once.
    every_property_value_appears_once!(Color, encoder);
    every_property_value_appears_once!(Nationality, encoder);
    every_property_value_appears_once!(Pet, encoder);
    every_property_value_appears_once!(Drink, encoder);
    every_property_value_appears_once!(Cigarette, encoder);
}

macro_rules! if_then_constraint {
    ($ifprop:ident :: $ifvalue:ident, $thenprop:ident :: $thenvalue:ident, $encoder:expr) => {
        for number in 0..5 {
            $encoder.add_constraint(If {
                cond: Pos(House {
                    number,
                    property: Property::$ifprop($ifprop::$ifvalue),
                }),
                then: Pos(House {
                    number,
                    property: Property::$thenprop($thenprop::$thenvalue),
                }),
            })
        }
    };
}

macro_rules! neighbor_if_then_constraint {
    ($ifprop:ident :: $ifvalue:ident, $thenprop:ident :: $thenvalue:ident, $encoder:expr) => {
        for number in 0..5 {
            let neighbors = [-1i32, 1]
                .iter()
                .map(|i| number + i)
                .filter(|&i| 0 <= i && i < 5)
                .map(|neighbor_number| {
                    Pos(House {
                        number: neighbor_number as u32,
                        property: Property::$thenprop($thenprop::$thenvalue),
                    })
                });

            let number = number as u32;

            $encoder.add_constraint(If {
                cond: Pos(House {
                    number,
                    property: Property::$ifprop($ifprop::$ifvalue),
                }),
                then: Or(neighbors),
            });
        }
    };
}

fn encode_specific_rules(encoder: &mut Encoder<House, impl Backend>) {
    // 1. The Englishman lives in the red house.
    if_then_constraint!(Nationality::English, Color::Red, encoder);

    // 2. The Swede keeps dogs.
    if_then_constraint!(Nationality::Swedish, Pet::Dogs, encoder);

    // 3. The Dane drinks tea.
    if_then_constraint!(Nationality::Danish, Drink::Tea, encoder);

    // 4. The green house is just to the left of the white one.
    for number in 0..4 {
        encoder.add_constraint(If {
            cond: Pos(House {
                number,
                property: Property::Color(Color::Green),
            }),
            then: Pos(House {
                number: number + 1,
                property: Property::Color(Color::White),
            }),
        });
    }

    // 5. The owner of the green house drinks coffee.
    if_then_constraint!(Color::Green, Drink::Coffee, encoder);

    // 6. The Pall Mall smoker keeps birds.
    if_then_constraint!(Cigarette::PallMall, Pet::Birds, encoder);

    // 7. The owner of the yellow house smokes Dunhills.
    if_then_constraint!(Color::Yellow, Cigarette::Dunhills, encoder);

    // 8. The man in the center house drinks milk.
    encoder.add_constraint(Pos(House {
        number: 2,
        property: Property::Drink(Drink::Milk),
    }));

    // 9. The Norwegian lives in the first house.
    encoder.add_constraint(Pos(House {
        number: 0,
        property: Property::Nationality(Nationality::Norwegian),
    }));

    // 10. The Blend smoker has a neighbor who keeps cats.
    neighbor_if_then_constraint!(Cigarette::Blend, Pet::Cats, encoder);

    // 11. The man who smokes Blue Masters drinks bier.
    if_then_constraint!(Cigarette::BlueMasters, Drink::Bier, encoder);

    // 12. The man who keeps horses lives next to the Dunhill smoker.
    neighbor_if_then_constraint!(Pet::Horses, Cigarette::Dunhills, encoder);

    // 13. The German smokes Prince.
    if_then_constraint!(Nationality::German, Cigarette::Prince, encoder);

    // 14. The Norwegian lives next to the blue house.
    neighbor_if_then_constraint!(Nationality::Norwegian, Color::Blue, encoder);

    // 15. The Blend smoker has a neighbor who drinks water.
    neighbor_if_then_constraint!(Cigarette::Blend, Drink::Water, encoder);
}

macro_rules! print_property {
    ($prop:ident, $number:expr, $model:expr) => {
        for p in $prop::iter() {
            if $model
                .var(House {
                    number: $number,
                    property: Property::$prop(p),
                })
                .unwrap()
            {
                print!(", {:?}", p);
            }
        }
    };
}

fn main() {
    let mut encoder = CadicalEncoder::new();

    encode_general_rules(&mut encoder);

    encode_specific_rules(&mut encoder);

    if let Some(model) = encoder.solve() {
        for number in 0..5 {
            print!("{}", number);

            print_property!(Color, number, model);
            print_property!(Nationality, number, model);
            print_property!(Pet, number, model);
            print_property!(Drink, number, model);
            print_property!(Cigarette, number, model);

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
