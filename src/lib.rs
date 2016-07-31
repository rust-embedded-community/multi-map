use std::collections::HashMap;
use std::collections::hash_map::Iter;
use std::hash::Hash;
use std::borrow::Borrow;

pub struct MultiMap<K1: Eq + Hash, K2: Eq + Hash, V> {
    value_map: HashMap<K1, (K2, V)>,
    key_map: HashMap<K2, K1>,
}

impl<K1: Eq + Hash + Clone, K2: Eq + Hash + Clone, V> MultiMap<K1, K2, V> {
    pub fn new() -> MultiMap<K1, K2, V> {
        MultiMap {
            value_map: HashMap::new(),
            key_map: HashMap::new(),
        }
    }

    pub fn insert(&mut self, key_one: K1, key_two: K2, value: V) {
        self.key_map.insert(key_two.clone(), key_one.clone());
        self.value_map.insert(key_one, (key_two, value));
    }

    pub fn get(&self, key: &K1) -> Option<&V> {
        let mut result = None;
        if let Some(pair) = self.value_map.get(key) {
            result = Some(&pair.1)
        }
        result
    }

    pub fn get_mut(&mut self, key: &K1) -> Option<&mut V> {
        let mut result = None;
        if let Some(pair) = self.value_map.get_mut(key) {
            result = Some(&mut pair.1)
        }
        result
    }

    pub fn get_alt(&self, key: &K2) -> Option<&V> {
        let mut result = None;
        if let Some(key_a) = self.key_map.get(key) {
            if let Some(pair) = self.value_map.get(&key_a) {
                result = Some(&pair.1)
            }
        }
        result
    }

    pub fn get_mut_alt(&mut self, key: &K2) -> Option<&mut V> {
        let mut result = None;
        if let Some(key_a) = self.key_map.get(key) {
            if let Some(pair) = self.value_map.get_mut(&key_a) {
                result = Some(&mut pair.1)
            }
        }
        result
    }

    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<V>
        where K1: Borrow<Q>,
              Q: Hash + Eq
    {
        let mut result = None;
        if let Some(pair) = self.value_map.remove(key) {
            self.key_map.remove(&pair.0);
            result = Some(pair.1)
        }
        result
    }

    pub fn remove_alt<Q: ?Sized>(&mut self, key: &Q) -> Option<V>
        where K2: Borrow<Q>,
              Q: Hash + Eq
    {
        let mut result = None;
        if let Some(key_a) = self.key_map.remove(key) {
            if let Some(pair) = self.value_map.remove(&key_a) {
                result = Some(pair.1)
            }
        }
        result
    }

    pub fn iter(&self) -> Iter<K1, (K2, V)> {
        self.value_map.iter()
    }
}

mod test {

    #[test]
    fn big_test() {
        use ::MultiMap;

        let mut map = MultiMap::new();

        map.insert(1, "One", String::from("Ein"));
        map.insert(2, "Two", String::from("Zwei"));
        map.insert(3, "Three", String::from("Drei"));

        assert!(*map.get(&1).unwrap() == String::from("Ein"));
        assert!(*map.get(&2).unwrap() == String::from("Zwei"));
        assert!(*map.get(&3).unwrap() == String::from("Drei"));

        map.get_mut_alt(&"One").expect("Weird").push_str("s");

        assert!(*map.get_alt(&"One").unwrap() == String::from("Eins"));
        assert!(*map.get_alt(&"Two").unwrap() == String::from("Zwei"));
        assert!(*map.get_alt(&"Three").unwrap() == String::from("Drei"));

        map.remove(&3);

        assert!(*map.get_alt(&"One").unwrap() == String::from("Eins"));
        assert!(*map.get_alt(&"Two").unwrap() == String::from("Zwei"));
        assert!(map.get_alt(&"Three") == None);
        assert!(map.get(&3) == None);

        assert!(map.remove_alt(&"Three") == None);
        assert!(*map.remove_alt(&"One").unwrap() == String::from("Eins"));

        map.get_mut(&2).expect("Weird?").push_str("!");

        assert!(map.get(&1) == None);
        assert!(*map.get(&2).unwrap() == String::from("Zwei!"));
        assert!(map.get_alt(&"Three") == None);
        assert!(map.get(&3) == None);

    }
}