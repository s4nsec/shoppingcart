import java.util.HashMap;


public class Cart{
    static class Item{
        //@ spec_public
        private Integer itemId;
        //@ spec_public
        private Integer quantity;
        //@ spec_public
        private Double price;

        //@ public invariant itemId >=0;
        //@ public invariant quantity >=0;
        //@ public invariant price >= 0;

        //@ requires itemId != null;
        //@ requires itemId >= 0;
        //@ requires quantity != null;
        //@ requires quantity >= 0;
        //@ requires price != null;
        //@ requires price >= 0;
        public Item(Integer itemId, Integer quantity, Double price) {
            this.itemId = itemId;
            this.quantity = quantity;
            this.price = price;
        }

        //@ ensures \result == this.quantity;
        public Integer getQuantity(){
            return this.quantity;
        }

        //@ ensures \result == this.itemId;
        public Integer getItemId(){
            return this.itemId;
        }

        //@ ensures \result == this.price;
        public Double getPrice() {
            return this.price;
        }

        //@ requires new_quantity != null;
        //@ requires new_quantity >= 0;
        //@ ensures this.quantity == new_quantity;
        public void setQuantity(Integer new_quantity) {
            this.quantity = new_quantity;
        }
    }

    static class ShoppingCart {
        //@ spec_public
        private Integer userId;
        //@ spec_public
        private HashMap<Integer, Item> items;

        //@ requires userId != null;
        //@ ensures this.userId == userId;
        //@ ensures this.items != null;
        public ShoppingCart(Integer userId) {
            this.userId = userId;
            this.items = new HashMap<Integer, Item>();
        }

        //@ requires itemId != null;
        //@ requires quantity != null;
        //@ requires itemId >= 0;
        //@ requires quantity >= 0;
        //@ requires price != null;
        //@ requires price >= 0;
        public void addItem(Integer itemId, Integer quantity, Double price) {
            if (items.containsKey(itemId)) {
                Item existingItem = items.get(itemId);
                existingItem.setQuantity(existingItem.getQuantity() + quantity);
            } else {
                Item newItem = new Item(itemId, quantity, price);
                items.put(itemId, newItem);
            }
        }

        //@ requires itemId != null;
        //@ requires itemId >= 0;
        //@ requires new_quantity != null;
        //@ requires new_quantity >= 0;
        public void updateQuantity(Integer itemId, Integer new_quantity) {
            this.items.get(itemId).setQuantity(new_quantity);
        }

        //@ requires itemId != null;
        //@ requires itemId >= 0;
        public void removeItem(Integer itemId) {
            this.items.remove(itemId);
        }

        // @ ensures \result >= 0.0;
        public Double getTotal() {
            double total = 0.0;
            // TODO: add loop invariant
            for (Item item : items.values()) {
                total += item.getPrice() * item.getQuantity();
            }
            return total;
        }
    }

    // public static void main(String[] args) {
    //     Integer userId = 1;
    //     ShoppingCart shoppingCart = new ShoppingCart(userId);
    //
    //     Item item2 = new Item(2, 4, 10.00);
    //     shoppingCart.addItem(item2.getItemId(), item2.getQuantity(), item2.getPrice());
    //
    //     shoppingCart.updateQuantity(2, 7);
    //
    //     shoppingCart.addItem(2, 5, 10.00);
    //
    //     shoppingCart.removeItem(2, 4);
    //
    //     Double total = shoppingCart.getTotal();
    //
    //     shoppingCart.checkOut();
    // }
}
