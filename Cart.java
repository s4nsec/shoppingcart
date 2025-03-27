import java.util.HashMap;

public class Cart {
    static class Item {
        private Integer itemId;
        private Integer quantity;
        private Double price;

        public Item(Integer itemId, Integer quantity, Double price) {
            this.itemId = itemId;
            this.quantity = quantity;
            this.price = price;
        }

        public Integer getQuantity() {
            return this.quantity;
        }

        public Integer getItemId() {
            return this.itemId;
        }

        public Double getPrice() {
            return this.price;
        }

        public void setQuantity(Integer new_quantity) {
            this.quantity = new_quantity;
        }
    }

    static class ShoppingCart {
        //@ spec_public
        private Integer userId;
        //@ spec_public
        private HashMap<Integer, Item> items;

        /*@
        @ requires userId != null;
        @ ensures this.userId == userId;
        @ ensures this.items != null;
        @*/
        public ShoppingCart(Integer userId) {
            this.userId = userId;
            this.items = new HashMap<Integer, Item>();
        }

        /*@
        @ requires itemId != null;
        @ requires quantity != null;
        @ requires itemId >= 0;
        @ requires quantity >= 0;
        @
        // @ ensures items.containsKey(itemId);
        // @ ensures items.get(itemId).getQuantity() == quantity;
        @*/
        public void addItem(Integer itemId, Integer quantity, Double price) {
            if (itemId < 0 || quantity < 0) {
                throw new IllegalArgumentException("Item ID and quantity must be non-negative.");
            }
            if (items.containsKey(itemId)) {
                Item existingItem = items.get(itemId);
                existingItem.setQuantity(existingItem.getQuantity() + quantity);
            } else {
                Item newItem = new Item(itemId, quantity, price);
                items.put(itemId, newItem);
            }
        }

        public void updateQuantity(Integer itemId, Integer new_quantity) {
            if (!items.containsKey(itemId)) {
                System.out.println("Item not found");
                return;
            }
            if (new_quantity <= 0) {
                items.remove(itemId);
            } else {
                items.get(itemId).setQuantity(new_quantity);
            }
        }

        /*@
        @ requires itemId != null;
        @*/
        public void removeItem(Integer itemId, Integer quantity) {
            if (!items.containsKey(itemId)) {
                System.out.println("Item not found");
                return;
            }
            Item item = items.get(itemId);
            if (quantity >= item.getQuantity()) {
                items.remove(itemId);
            } else {
                item.setQuantity(item.getQuantity() - quantity);
            }
        }

        /*@
        @ ensures \result >= 0.0;
        @*/
        public Double getTotal() {
            double total = 0.0;
            for (Item item : items.values()) {
                total += item.getPrice() * item.getQuantity();
            }
            return total;
        }

        /*@
        @ ensures items.isEmpty();
        @*/
        public void checkOut() {
            double total = getTotal();
            System.out.println("Your total is: " + total);
            items.clear();
        }
    }

    private static void printCartContents(ShoppingCart cart) {
        if (cart.items.isEmpty()) {
            System.out.println("Cart is empty.");
        } else {
            System.out.println("Cart Contents:");
            for (Item item : cart.items.values()) {
                double totalCost = item.getPrice() * item.getQuantity();
                System.out.println("Item ID: " + item.getItemId() +
                                   ", Quantity: " + item.getQuantity() +
                                   ", Unit Price: " + item.getPrice() +
                                   ", Total Cost: " + totalCost);
            }
        }
        System.out.println("-----------------------------------------");
    }

    public static void main(String[] args) {
        Integer userId = 1;
        ShoppingCart shoppingCart = new ShoppingCart(userId);

        Item item2 = new Item(2, 4, 10.00);
        shoppingCart.addItem(item2.getItemId(), item2.getQuantity(), item2.getPrice());
        System.out.println("After adding item2:");
        printCartContents(shoppingCart);

        shoppingCart.updateQuantity(2, 7);
        System.out.println("After updating quantity of item2 to 7:");
        printCartContents(shoppingCart);

        shoppingCart.addItem(2, 5, 10.00);
        System.out.println("After adding 5 more of item2:");
        printCartContents(shoppingCart);

        shoppingCart.removeItem(2, 4);
        System.out.println("After removing 4 units from item2:");
        printCartContents(shoppingCart);

        Double total = shoppingCart.getTotal();
        System.out.println("Total cost of items in the cart: " + total);

        shoppingCart.checkOut();
        System.out.println("After checkout:");
        printCartContents(shoppingCart);
    }
}
